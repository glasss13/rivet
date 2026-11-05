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
  registers : Reg → Nat
  zeroFlag : Bool
  memory : Nat → Fin 256
  readable : Nat → Bool
  status : ExecutionStatus
  readHistory : List Access

def put (state : MachineState) (register : Reg) (value : Nat) : MachineState :=
  { state with registers := fun otherRegister =>
      if otherRegister = register then value % word else state.registers otherRegister }
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
    let result := Nat.xor (state.registers destination.parent % 2^32) (state.registers sourceRegister.parent % 2^32)
    next { put state destination.parent result with zeroFlag := result == 0 }
  | .test leftRegister rightRegister =>
    next { state with zeroFlag := (state.registers leftRegister &&& state.registers rightRegister) == 0 }
  | .movzx destination memoryOperand =>
    let address := state.registers memoryOperand.base
    if address < word && state.readable address then
      next { put state destination.parent (state.memory address).val with readHistory := state.readHistory ++ [⟨address,1⟩] }
    else { state with status := .fault }
  | .add destination sourceRegister =>
    let result := (state.registers destination + state.registers sourceRegister) % word
    next { put state destination result with zeroFlag := result == 0 }
  | .inc destination =>
    let result := (state.registers destination + 1) % word
    next { put state destination result with zeroFlag := result == 0 }
  | .dec destination =>
    -- Keep the symbolic operand last to avoid expanding a word-sized numeral during reduction.
    let result := (word - 1 + state.registers destination) % word
    next { put state destination result with zeroFlag := result == 0 }
  | .jz target => { state with status := if state.zeroFlag then .running target else state.status.advance }
  | .jnz target => { state with status := if state.zeroFlag then state.status.advance else .running target }
  | .ret =>
    let address := state.registers .rsp
    if address + 8 ≤ word && (List.range 8).all (fun offset => state.readable (address+offset)) then
      { put state .rsp (address+8) with
        status := .returned (read64 state.memory address)
        readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }

def step (program : Program) (state : MachineState) : MachineState :=
  match state.status with
  | .running index => match program[index]? with
    | some instruction => stepOp instruction.op state
    | none => { state with status := .fault }
  | _ => state

def run (program : Program) (steps : Nat) (state : MachineState) : MachineState :=
  match steps with
  | 0 => state
  | remainingSteps+1 => run program remainingSteps (step program state)

/-- The little-endian address stored in the current stack return slot. -/
def MachineState.returnAddress (state : MachineState) : Nat :=
  read64 state.memory (state.registers .rsp)

def MachineState.ValidReturnSlot (state : MachineState) : Prop :=
  state.registers .rsp + 8 ≤ word ∧
    (List.range 8).all (fun offset => state.readable (state.registers .rsp + offset)) = true

/-- Record update used to express register values in instruction postconditions. -/
def MachineState.write (state : MachineState) (register : Reg) (value : Nat) : MachineState :=
  { state with registers := fun other => if other = register then value else state.registers other }

def AtInstruction (state : MachineState) (index : Nat) : Prop :=
  state.status = .running index

def execute (program : Program) (steps : Nat) (initial : MachineState) : MachineState :=
  run program steps initial

-- Only ZF is observable by this language. No instruction writes memory.
theorem step_memory (program : Program) (state : MachineState) : (step program state).memory = state.memory := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      cases instruction.op <;> simp [stepOp, next, put] <;> split <;> rfl
    · rfl
  · rfl

theorem run_memory (program : Program) (steps : Nat) (state : MachineState) :
    (run program steps state).memory = state.memory := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis => rw [run, inductionHypothesis, step_memory]

theorem run_add (program : Program) (firstSteps secondSteps : Nat) (state : MachineState) :
    run program (firstSteps+secondSteps) state = run program secondSteps (run program firstSteps state) := by
  induction firstSteps generalizing state with
  | zero => simp [run]
  | succ firstSteps inductionHypothesis => simpa [Nat.succ_add, run] using inductionHypothesis (step program state)

end Rivet
