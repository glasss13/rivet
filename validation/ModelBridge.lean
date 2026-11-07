module
public import Rivet
public import Json
meta import JsonDeriving

@[expose] public section
open Rivet Json

deriving instance FromJson for Reg
deriving instance FromJson for Reg8
deriving instance FromJson for Reg32
deriving instance FromJson for Reg16
deriving instance FromJson for Xmm
deriving instance FromJson for XmmMove
deriving instance FromJson for Width
deriving instance FromJson for Scale
deriving instance FromJson for Address
deriving instance FromJson for BinaryOp
deriving instance FromJson for ShiftOp
deriving instance FromJson for Operand
deriving instance FromJson for Condition
deriving instance FromJson for Op
deriving instance FromJson for Instruction
deriving instance FromJson for FlagValues

structure Request where
  program : Array Instruction
  registers : Array Nat
  xmmRegisters : Array (Array Nat)
  signFlag : Bool
  zeroFlag : Bool
  carryFlag : Bool
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
  status := state.status
  memory := (Array.range memorySize).map (fun offset => (state.memory (memoryBase + offset)).val) }

def evaluate (request : Request) : Except String (Array SnapshotOutput) := do
  unless request.registers.size == 16 && request.steps ≤ 64 do
    throw "invalid registers or step budget"
  unless request.registers.all (· < 2^64) do throw "register value exceeds 64 bits"
  unless request.xmmRegisters.size == 16 &&
      request.xmmRegisters.all (fun words => words.size == 4 && words.all (· < 2^32)) do
    throw "invalid XMM register values"
  unless request.memory.size ≤ 65536 && request.memory.all (· < 256) do
    throw "invalid memory"
  let program := request.program.toList
  let some first := program.head? | throw "empty program"
  let initial : MachineState := {
    registers := fun register => BitVec.ofNat 64 (request.registers[registerOrder.toList.idxOf register]!)
    xmmRegisters := fun register => BitVec.ofNat 128
      ((request.xmmRegisters[xmmOrder.toList.idxOf register]!).foldr (fun word value => word + 2^32 * value) 0)
    signFlag := request.signFlag
    zeroFlag := request.zeroFlag
    carryFlag := request.carryFlag
    writable := fun address => request.writableBase ≤ address &&
      address < request.memoryBase + request.memory.size
    readable := fun address => request.memoryBase ≤ address &&
      address < request.memoryBase + request.memory.size
    memory := fun address =>
      let value := if request.memoryBase ≤ address then
        request.memory[address - request.memoryBase]?.getD 0 else 0
      ⟨value % 256, Nat.mod_lt _ (by decide)⟩
    status := .running first.address
    readHistory := [] }
  let mut current := initial
  let mut observations := #[snapshot request.memoryBase request.memory.size initial]
  for index in [:request.steps] do
    if !current.status.isRunning then break
    let some undefinedFlags := request.nativeFlags[index]?
      | throw "missing native flag observation"
    current := step program current undefinedFlags
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
