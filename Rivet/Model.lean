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
  memory : Nat → Fin 256
  readable : Nat → Bool
  status : ExecutionStatus
  readHistory : List Access

/-- Update one register; its width is enforced by the value's type. -/
def MachineState.write (state : MachineState) (register : Reg) (value : BitVec 64) : MachineState :=
  { state with registers := fun otherRegister =>
      if otherRegister = register then value else state.registers otherRegister }

def ExecutionStatus.isRunning : ExecutionStatus → Bool
  | .running _ => true
  | _ => false

def ExecutionStatus.advance : ExecutionStatus → ExecutionStatus
  | .running index => .running (index + 1)
  | stopped => stopped

def next (state : MachineState) : MachineState := { state with status := state.status.advance }
def read64 (memory : Nat → Fin 256) (address : Nat) : Nat :=
  (List.range 8).foldr (fun offset value => (memory (address+offset)).val + 256*value) 0

def stepOp (operation : Op) (state : MachineState) : MachineState :=
  match operation with
  | .xor destination sourceRegister =>
    let result := (state.registers destination.parent).setWidth 32 ^^^
      (state.registers sourceRegister.parent).setWidth 32
    next { state.write destination.parent (result.setWidth 64) with zeroFlag := result == 0 }
  | .test leftRegister rightRegister =>
    next { state with zeroFlag := (state.registers leftRegister &&& state.registers rightRegister) == 0 }
  | .movzx destination memoryOperand =>
    let address := (state.registers memoryOperand.base).toNat
    if state.readable address then
      next { state.write destination.parent (BitVec.ofNat 64 (state.memory address).val) with readHistory := state.readHistory ++ [⟨address,1⟩] }
    else { state with status := .fault }
  | .add destination sourceRegister =>
    let result := state.registers destination + state.registers sourceRegister
    next { state.write destination result with zeroFlag := result == 0 }
  | .inc destination =>
    let result := state.registers destination + 1
    next { state.write destination result with zeroFlag := result == 0 }
  | .dec destination =>
    let result := state.registers destination - 1
    next { state.write destination result with zeroFlag := result == 0 }
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

-- Only ZF is observable by this language. No instruction writes memory.
theorem step_memory (program : Program) (state : MachineState) : (step program state).memory = state.memory := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      cases instruction.op <;> simp [stepOp, next, MachineState.write] <;> split <;> rfl
    · rfl
  · rfl

theorem execute_memory (program : Program) (steps : Nat) (state : MachineState) :
    (execute program steps state).memory = state.memory := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis => rw [execute, inductionHypothesis, step_memory]

theorem execute_add (program : Program) (firstSteps secondSteps : Nat) (state : MachineState) :
    execute program (firstSteps+secondSteps) state = execute program secondSteps (execute program firstSteps state) := by
  induction firstSteps generalizing state with
  | zero => simp [execute]
  | succ firstSteps inductionHypothesis => simpa [Nat.succ_add, execute] using inductionHypothesis (step program state)

end Rivet
