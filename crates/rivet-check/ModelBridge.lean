module
public import Rivet
public import Json
meta import JsonDeriving

@[expose] public section
open Rivet Json

-- Addresses and exit codes travel as JSON numbers.
instance : FromJson (BitVec 64) where
  fromJson? json := do
    let value : Nat ← fromJson? json
    unless value < 2^64 do throw "address exceeds 64 bits"
    return BitVec.ofNat 64 value
instance : ToJson (BitVec width) where
  toJson value := toJson value.toNat

deriving instance FromJson for FlagValues

structure Request where
  codeBase : Nat
  code : Array Nat
  stopAddress : Nat
  registers : Array Nat
  xmmRegisters : Array (Array Nat)
  signFlag : Bool
  zeroFlag : Bool
  carryFlag : Bool
  overflowFlag : Bool
  memoryBase : Nat
  writableBase : Nat
  memory : Array Nat
  steps : Nat
  nativeFlags : Array FlagValues
  deriving FromJson
deriving instance ToJson for ExecutionStatus
structure SnapshotOutput where
  registers : Array Nat
  xmmRegisters : Array (Array Nat)
  signFlag : Bool
  zeroFlag : Bool
  carryFlag : Bool
  overflowFlag : Bool
  status : ExecutionStatus
  memory : Array Nat
  deriving ToJson

def registerOrder : Array Reg := #[.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .rsp,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
def xmmOrder : Array Xmm := #[.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
  .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]
def snapshot (memoryBase memorySize : Nat) (state : MachineState) : SnapshotOutput := {
  registers := registerOrder.map (fun register => (state.registers register).toNat)
  xmmRegisters := xmmOrder.map fun register =>
    (Array.range 4).map fun index => (state.xmmRegisters register).toNat / 2^(32*index) % 2^32
  signFlag := state.signFlag
  zeroFlag := state.zeroFlag
  carryFlag := state.carryFlag
  overflowFlag := state.overflowFlag
  status := state.status
  memory := (Array.range memorySize).map (fun offset => (state.memory (BitVec.ofNat 64 (memoryBase + offset))).val) }

def evaluate (request : Request) : Except String (Array SnapshotOutput) := do
  unless request.registers.size == 16 && request.steps ≤ 64 do
    throw "invalid registers or step budget"
  unless request.registers.all (· < 2^64) do throw "register value exceeds 64 bits"
  unless request.xmmRegisters.size == 16 &&
      request.xmmRegisters.all (fun words => words.size == 4 && words.all (· < 2^32)) do
    throw "invalid XMM register values"
  unless request.memory.size ≤ 65536 && request.memory.all (· < 256) do
    throw "invalid memory"
  let codeEnd := request.codeBase + request.code.size
  let dataEnd := request.memoryBase + request.memory.size
  unless !request.code.isEmpty && request.code.all (· < 256) && codeEnd ≤ 2^64 do
    throw "invalid code"
  unless request.memoryBase ≤ request.writableBase && request.writableBase ≤ dataEnd && dataEnd ≤ 2^64 do
    throw "invalid data range"
  unless request.memory.isEmpty || codeEnd ≤ request.memoryBase || dataEnd ≤ request.codeBase do
    throw "code overlaps data"
  let inCode (a : Nat) := request.codeBase ≤ a && a < codeEnd
  let memory : Memory := fun address =>
    let a := address.toNat
    if inCode a then Fin.ofNat 256 request.code[a - request.codeBase]!
    else if request.memoryBase ≤ a && a < dataEnd then Fin.ofNat 256 request.memory[a - request.memoryBase]!
    else 0
  let kernel : Kernel := ⟨fun address =>
    let a := address.toNat
    if inCode a then .readExec
    else if request.memoryBase ≤ a && a < request.writableBase then .readOnly
    else if request.writableBase ≤ a && a < dataEnd then .readWrite
    else .unmapped⟩
  let initial : MachineState := {
    registers := fun register => BitVec.ofNat 64 (request.registers[registerOrder.toList.idxOf register]!)
    xmmRegisters := fun register => BitVec.ofNat 128
      ((request.xmmRegisters[xmmOrder.toList.idxOf register]!).foldr (fun word value => word + 2^32 * value) 0)
    signFlag := request.signFlag
    zeroFlag := request.zeroFlag
    carryFlag := request.carryFlag
    overflowFlag := request.overflowFlag
    memory
    kernel
    status := .running (BitVec.ofNat 64 request.codeBase) }
  let mut current := initial
  let mut observations := #[snapshot request.memoryBase request.memory.size initial]
  for index in [:request.steps] do
    let .running address := current.status | break
    if address == BitVec.ofNat 64 request.stopAddress then break
    let some undefinedFlags := request.nativeFlags[index]?
      | throw "missing native flag observation"
    current := step current undefinedFlags
    observations := observations.push (snapshot request.memoryBase request.memory.size current)
  unless observations.size == request.nativeFlags.size + 1 do
    throw "unused native flag observations"
  return observations

def respond (line : String) : Json :=
  match (Json.parse line).mapError toString >>= fromJson? >>= evaluate with
  | .ok observations => Json.mkObj [("snapshots", toJson observations)]
  | .error message => Json.mkObj [("error", toJson message)]
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let line ← input.getLine
  output.putStrLn (respond line).compress
  output.flush
