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
deriving instance FromJson for Width
deriving instance FromJson for Scale
deriving instance FromJson for Address
deriving instance FromJson for Operand
deriving instance FromJson for Op

structure Request where
  program : Array Op
  registers : Array Nat
  zeroFlag : Bool
  carryFlag : Bool
  memoryBase : Nat
  writableBase : Nat
  memory : Array Nat
  steps : Nat
  deriving FromJson
deriving instance ToJson for ExecutionStatus
structure SnapshotOutput where
  registers : Array Nat
  zeroFlag : Bool
  carryFlag : Bool
  status : ExecutionStatus
  memory : Array Nat
  deriving ToJson

def registerOrder : Array Reg := #[.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .rsp,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
def snapshot (memoryBase memorySize : Nat) (state : MachineState) : SnapshotOutput := {
  registers := registerOrder.map (fun register => (state.registers register).toNat)
  zeroFlag := state.zeroFlag
  carryFlag := state.carryFlag
  status := state.status
  memory := (Array.range memorySize).map (fun offset => (state.memory (memoryBase + offset)).val) }

def evaluate (request : Request) : Except String (Array SnapshotOutput) := do
  unless request.registers.size == 16 && request.steps ≤ 64 do
    throw "invalid registers or step budget"
  unless request.registers.all (· < 2^64) do throw "register value exceeds 64 bits"
  unless request.memory.size ≤ 65536 && request.memory.all (· < 256) do
    throw "invalid memory"
  let program := request.program.toList.map fun operation => ⟨operation, 0⟩
  let initial : MachineState := {
    registers := fun register => BitVec.ofNat 64 (request.registers[registerOrder.toList.idxOf register]!)
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
    status := .running 0
    readHistory := [] }
  let mut current := initial
  let mut observations := #[snapshot request.memoryBase request.memory.size initial]
  for _ in [:request.steps] do
    if !current.status.isRunning then break
    current := step program current
    observations := observations.push (snapshot request.memoryBase request.memory.size current)
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
