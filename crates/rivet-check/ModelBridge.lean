module
public import Rivet
public import Json
meta import JsonDeriving

@[expose] public section
open Rivet Json

-- Addresses and exit codes travel as JSON numbers, memory contents as hex strings.
instance : FromJson (BitVec width) where
  fromJson? json := do
    let value : Nat ← fromJson? json
    unless value < 2^width do throw s!"value exceeds {width} bits"
    return BitVec.ofNat width value
instance : ToJson (BitVec width) where
  toJson value := toJson value.toNat
instance : FromJson ByteArray where
  fromJson? json := do
    let digits := (← fromJson? json : String).toUTF8
    unless digits.size % 2 == 0 do throw "odd-length hex string"
    let nibble (character : UInt8) : Except String UInt8 :=
      if 48 ≤ character && character ≤ 57 then pure (character - 48)
      else if 97 ≤ character && character ≤ 102 then pure (character - 87)
      else if 65 ≤ character && character ≤ 70 then pure (character - 55)
      else throw "invalid hex digit"
    let mut bytes := ByteArray.emptyWithCapacity (digits.size / 2)
    for index in [:digits.size / 2] do
      let high ← nibble digits[2 * index]!
      let low ← nibble digits[2 * index + 1]!
      bytes := bytes.push (16 * high + low)
    return bytes

deriving instance FromJson for Access
inductive ObservedStatus where
  | running (address : BitVec 64)
  | exited (code : BitVec 8)
  | fault
  | signal (number : Int) (address : BitVec 64)
  deriving BEq, FromJson, ToJson

def toObserved : ExecutionStatus → ObservedStatus
  | .running address => .running address
  | .exited code => .exited code
  | .fault => .fault

def ObservedStatus.toExecution : ObservedStatus → ExecutionStatus
  | .running address => .running address
  | .exited code => .exited code
  | .fault | .signal .. => .fault

instance : ToJson Segment where
  toJson segment := Json.mkObj [("vaddr", toJson segment.vaddr), ("memsz", toJson segment.memsz),
    ("offset", toJson segment.offset), ("filesz", toJson segment.filesz),
    ("writable", toJson segment.writable), ("executable", toJson segment.executable)]
deriving instance ToJson for Layout

structure Mapping where
  base : Nat
  access : Access
  bytes : ByteArray
  deriving FromJson

-- A machine state as Linux and the model both report it. `writes` are the writable bytes the last
-- step changed: with the mappings, that is all of memory.
structure Snapshot where
  registers : Array Nat
  xmmRegisters : Array (Array Nat)
  signFlag : Bool
  zeroFlag : Bool
  carryFlag : Bool
  overflowFlag : Bool
  status : ObservedStatus
  writes : Array (Nat × Nat)
  deriving BEq, FromJson, ToJson

-- The memory Linux mapped, the state it started in, and the state it reached after each instruction.
structure Request where
  mappings : Array Mapping
  start : Snapshot
  steps : Array Snapshot
  deriving FromJson

-- The first step whose state the model computes differently, and whether its instruction decoded.
structure Mismatch where
  step : Nat
  model : Snapshot
  decoded : Bool
  deriving ToJson

def registerOrder : Array Reg := #[.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .rsp,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
def xmmOrder : Array Xmm := #[.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
  .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def snapshot (state : MachineState) (writes : Array (Nat × Nat)) : Snapshot where
  registers := registerOrder.map fun register => (state.registers register).toNat
  xmmRegisters := xmmOrder.map fun register =>
    (Array.range 4).map fun index => (state.xmmRegisters register).toNat / 2^(32*index) % 2^32
  signFlag := state.signFlag
  zeroFlag := state.zeroFlag
  carryFlag := state.carryFlag
  overflowFlag := state.overflowFlag
  status := toObserved state.status
  writes

@[inline] def Mapping.holds (mapping : Mapping) (address : BitVec 64) : Bool :=
  mapping.base ≤ address.toNat && address.toNat < mapping.base + mapping.bytes.size

def machine (mappings : Array Mapping) (observed : Snapshot) : MachineState where
  registers register := BitVec.ofNat 64 observed.registers[registerOrder.toList.idxOf register]!
  xmmRegisters register := BitVec.ofNat 128
    (observed.xmmRegisters[xmmOrder.toList.idxOf register]!.foldr (fun word value => word + 2^32 * value) 0)
  signFlag := observed.signFlag
  zeroFlag := observed.zeroFlag
  carryFlag := observed.carryFlag
  overflowFlag := observed.overflowFlag
  memory address := mappings.foldl (init := 0) fun byte mapping =>
    if mapping.holds address then Fin.ofNat 256 mapping.bytes[address.toNat - mapping.base]!.toNat else byte
  kernel := ⟨fun address => mappings.foldl (init := .unmapped) fun access mapping =>
    if mapping.holds address then mapping.access else access⟩
  status := observed.status.toExecution

inductive DecodeOutcome where
  | ok
  | noExec
  | rejected
  deriving BEq

def decodeOutcome (code : Code) (address : BitVec 64) : DecodeOutcome :=
  let rec read : Nat → Nat → DecodeState → DecodeOutcome
    | 0, _, _ => .rejected
    | fuel+1, offset, state =>
      match code (address + BitVec.ofNat 64 offset) with
      | none => .noExec
      | some byte =>
        match feed state byte with
        | .reject => .rejected
        | .done _ => .ok
        | .more next => read fuel (offset + 1) next
  read 15 0 (.opcode {})

-- Every writable byte is read back after every step, so a stray write cannot hide; holding the
-- result as bytes again keeps a long run from stacking one closure per store.
def settle (mappings : Array Mapping) (memory : Memory) : Array Mapping × Array (Nat × Nat) := Id.run do
  let mut settled := #[]
  let mut writes := #[]
  for mapping in mappings do
    let mut bytes := mapping.bytes
    if mapping.access == .readWrite then
      for offset in [:bytes.size] do
        -- `BitVec.ofNat 64` would compute `2^64` afresh for each byte.
        let byte := (memory (UInt64.ofNat (mapping.base + offset)).toBitVec).val.toUInt8
        if byte != bytes[offset]! then
          writes := writes.push (mapping.base + offset, byte.toNat)
          bytes := bytes.set! offset byte
    settled := settled.push { mapping with bytes }
  return (settled, writes)

def evaluate (request : Request) : Option Mismatch := Id.run do
  let mut mappings := request.mappings
  let mut current := machine mappings request.start
  for observed in request.steps, index in [1:request.steps.size + 1] do
    let outcome := match current.status with
      | .running address => decodeOutcome current.code address
      | _ => .ok
    -- Linux's values stand in for the flags the instruction leaves undefined.
    let next := step current ⟨observed.signFlag, observed.zeroFlag, observed.overflowFlag⟩
    let (settled, writes) := settle mappings next.memory
    let model := snapshot next writes
    if outcome == .rejected || model != observed then
      return some { step := index, model, decoded := outcome != .rejected }
    mappings := settled
    current := machine mappings model
  return none

def layout (file : ByteArray) : Option Layout :=
  Exe.layout {
    size := file.size
    pages := (List.range ((file.size + 4095) / 4096)).map fun page =>
      (file.extract (4096 * page) (4096 * page + 4096)).data.foldr (fun byte value => byte.toNat + 256 * value) 0 }

-- With a path, the layout Lean reads from that ELF file; otherwise, a request on standard input.
def main : List String → IO Unit
  | [path] => do IO.println (toJson (layout (← IO.FS.readBinFile path))).compress
  | _ => do
    match (Json.parse (← (← IO.getStdin).getLine)).mapError toString >>= fromJson? with
    | .ok request => IO.println (toJson (evaluate request)).compress
    | .error message => throw (IO.userError message)
