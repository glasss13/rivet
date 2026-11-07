module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

inductive ExecutionStatus where
  | running (instructionIndex : Nat)
  | returned (address : Nat)
  | fault
  deriving DecidableEq, Repr
structure MachineState where
  registers : Reg → BitVec 64
  zeroFlag : Bool
  carryFlag : Bool := false
  memory : Nat → Fin 256
  readable : Nat → Bool
  writable : Nat → Bool := fun _ => false
  status : ExecutionStatus
  readHistory : List Access

/-- Update one register; its width is enforced by the value's type. -/
def MachineState.write (state : MachineState) (register : Reg) (value : BitVec 64) : MachineState :=
  { state with registers := fun otherRegister =>
      if otherRegister = register then value else state.registers otherRegister }

/-- Update one byte; permission checks belong to the instruction semantics. -/
def MachineState.storeByte (state : MachineState) (address : Nat) (value : Fin 256) : MachineState :=
  { state with memory := fun otherAddress => if otherAddress = address then value else state.memory otherAddress }

def ExecutionStatus.isRunning : ExecutionStatus → Bool
  | .running _ => true
  | _ => false

def ExecutionStatus.advance : ExecutionStatus → ExecutionStatus
  | .running index => .running (index + 1)
  | stopped => stopped

def next (state : MachineState) : MachineState := { state with status := state.status.advance }
def read64 (memory : Nat → Fin 256) (address : Nat) : Nat :=
  (List.range 8).foldr (fun offset value => (memory (address+offset)).val + 256*value) 0

def Address.evaluate (address : Address) (registers : Reg → BitVec 64) : BitVec 64 :=
  (address.base.map registers).getD 0 +
    (address.index.map registers).getD 0 * BitVec.ofNat 64 address.scale.value +
    BitVec.ofInt 64 address.displacement

/-- Multi-byte accesses must fit the address space and have permission for every byte. -/
def permits (permission : Nat → Bool) (address size : Nat) : Bool :=
  address + size ≤ word && (List.range size).all (fun offset => permission (address + offset))

def readMemory (memory : Nat → Fin 256) (address : Nat) (width : Width) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range width.bytes).foldr
    (fun offset value => (memory (address + offset)).val + 256 * value) 0)

/-- Write a whole value after its complete range has passed permission checks. -/
def MachineState.writeMemory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : MachineState :=
  (List.range width.bytes).foldl (fun current offset =>
    current.storeByte (address + offset)
      ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩) state

def MachineState.readOperand (state : MachineState) : Operand → BitVec 64
  | .reg8 register => ((state.registers register.parent).setWidth 8).setWidth 64
  | .reg16 register => ((state.registers register.parent).setWidth 16).setWidth 64
  | .reg32 register => ((state.registers register.parent).setWidth 32).setWidth 64
  | .reg64 register => state.registers register
  | .memory width address => readMemory state.memory (address.evaluate state.registers).toNat width
  | .immediate value => BitVec.ofInt 64 value

def MachineState.writeOperand (state : MachineState) (operand : Operand) (value : BitVec 64) : MachineState :=
  match operand with
  | .reg8 register => state.write register.parent
      ((state.registers register.parent &&& ~~~(255#64)) ||| ((value.setWidth 8).setWidth 64))
  | .reg16 register => state.write register.parent
      ((state.registers register.parent &&& ~~~(65535#64)) ||| ((value.setWidth 16).setWidth 64))
  | .reg32 register => state.write register.parent ((value.setWidth 32).setWidth 64)
  | .reg64 register => state.write register value
  | .memory width address => state.writeMemory (address.evaluate state.registers).toNat width value
  | .immediate _ => state

def MachineState.canRead (state : MachineState) : Operand → Bool
  | .memory width address => permits state.readable (address.evaluate state.registers).toNat width.bytes
  | _ => true

def MachineState.canWrite (state : MachineState) : Operand → Bool
  | .memory width address => permits state.writable (address.evaluate state.registers).toNat width.bytes
  | .immediate _ => false
  | _ => true

def MachineState.recordRead (state : MachineState) : Operand → MachineState
  | .memory width address => { state with readHistory := state.readHistory ++
      [⟨(address.evaluate state.registers).toNat, width.bytes⟩] }
  | _ => state

def stepOp (operation : Op) (state : MachineState) : MachineState :=
  match operation with
  | .xor destination sourceRegister =>
    let result := (state.registers destination.parent).setWidth 32 ^^^
      (state.registers sourceRegister.parent).setWidth 32
    next { state.write destination.parent (result.setWidth 64) with zeroFlag := result == 0, carryFlag := false }
  | .test leftRegister rightRegister =>
    next { state with zeroFlag := (state.registers leftRegister &&& state.registers rightRegister) == 0, carryFlag := false }
  | .movzx destination memoryOperand =>
    let address := (memoryOperand.evaluate state.registers).toNat
    if state.readable address then
      next { state.write destination.parent (BitVec.ofNat 64 (state.memory address).val) with readHistory := state.readHistory ++ [⟨address,1⟩] }
    else { state with status := .fault }
  | .mov destination source =>
    if validMove destination source && state.canRead source && state.canWrite destination then
      -- Read and address calculation use the pre-instruction registers, including aliases.
      let result := state.writeOperand destination (state.readOperand source)
      next { result with readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .cmp leftRegister rightRegister =>
    next { state with
      zeroFlag := state.registers leftRegister == state.registers rightRegister
      carryFlag := state.registers leftRegister < state.registers rightRegister }
  | .add destination sourceRegister =>
    let result := state.registers destination + state.registers sourceRegister
    next { state.write destination result with
      zeroFlag := result == 0
      carryFlag := result < state.registers destination }
  | .inc destination =>
    let result := state.registers destination + 1
    next { state.write destination result with zeroFlag := result == 0 }
  | .dec destination =>
    let result := state.registers destination - 1
    next { state.write destination result with zeroFlag := result == 0 }
  | .jb target => { state with status := if state.carryFlag then .running target else state.status.advance }
  | .jz target => { state with status := if state.zeroFlag then .running target else state.status.advance }
  | .jnz target => { state with status := if state.zeroFlag then state.status.advance else .running target }
  | .ret =>
    let address := (state.registers .rsp).toNat
    if address + 8 ≤ word && (List.range 8).all (fun offset => state.readable (address+offset)) then
      { state.write .rsp (state.registers .rsp + 8) with
        status := .returned (read64 state.memory address)
        readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }

def step (program : Program) (state : MachineState) : MachineState :=
  match state.status with
  | .running index => match program[index]? with
    | some instruction => stepOp instruction.op state
    | none => { state with status := .fault }
  | _ => state

def execute (program : Program) (steps : Nat) (state : MachineState) : MachineState :=
  match steps with
  | 0 => state
  | remainingSteps+1 => execute program remainingSteps (step program state)

/-- The little-endian address stored in the current stack return slot. -/
def MachineState.returnAddress (state : MachineState) : Nat :=
  read64 state.memory (state.registers .rsp).toNat

def MachineState.ValidReturnSlot (state : MachineState) : Prop :=
  (state.registers .rsp).toNat + 8 ≤ word ∧
    (List.range 8).all (fun offset => state.readable ((state.registers .rsp).toNat + offset)) = true

def AtInstruction (state : MachineState) (index : Nat) : Prop :=
  state.status = .running index

theorem execute_add (program : Program) (firstSteps secondSteps : Nat) (state : MachineState) :
    execute program (firstSteps+secondSteps) state = execute program secondSteps (execute program firstSteps state) := by
  induction firstSteps generalizing state with
  | zero => simp [execute]
  | succ firstSteps inductionHypothesis => simpa [Nat.succ_add, execute] using inductionHypothesis (step program state)

end Rivet
