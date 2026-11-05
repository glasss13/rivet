module
public import Rivet.Model
import Rivet.Safety
@[expose] public section
namespace Rivet

abbrev InstructionAt (program : Program) (index : Nat) (instruction : Op) : Prop :=
  (program[index]?).map Instruction.op = some instruction

/-- Executing from a state satisfying the precondition establishes the postcondition. -/
structure Ensures (program : Program) (steps : Nat)
    (precondition postcondition : MachineState → Prop) : Prop where
  run : ∀ initial, precondition initial → postcondition (execute program steps initial)

theorem Ensures.seq (first : Ensures program firstSteps precondition intermediate)
    (second : Ensures program secondSteps intermediate postcondition) :
    Ensures program (firstSteps + secondSteps) precondition postcondition := by
  constructor
  intro initial preconditionHolds
  simpa only [execute, run_add] using
    second.run (execute program firstSteps initial) (first.run initial preconditionHolds)

theorem Ensures.consequence (contract : Ensures program steps precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures program steps strongerPrecondition weakerPostcondition :=
  ⟨fun initial assumption => weakenPostcondition _ (contract.run initial (strengthenPrecondition _ assumption))⟩

@[simp] theorem execute_zero (program : Program) (initial : MachineState) :
    execute program 0 initial = initial := by rfl

theorem execute_execute (program : Program) (later earlier : Nat) (initial : MachineState) :
    execute program later (execute program earlier initial) =
      execute program (earlier + later) initial := (run_add program earlier later initial).symm

@[simp] theorem execute_returned (program : Program) (steps : Nat) (initial : MachineState)
    (returned : initial.status = .returned address) : execute program steps initial = initial :=
  run_stopped program steps initial (by simp [returned, ExecutionStatus.isRunning])

@[simp] theorem execute_fault (program : Program) (steps : Nat) (initial : MachineState)
    (faulted : initial.status = .fault) : execute program steps initial = initial :=
  run_stopped program steps initial (by simp [faulted, ExecutionStatus.isRunning])

theorem execute_reads_mono (program : Program) (steps : Nat) (initial : MachineState) (access : Access)
    (recorded : access ∈ initial.readHistory) : access ∈ (execute program steps initial).readHistory :=
  run_reads_monotone program initial steps access recorded

theorem execute_preserves_register (program : Program) (steps : Nat) (initial : MachineState)
    (register : Reg) (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    (execute program steps initial).registers register = initial.registers register := by
  apply run_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

private theorem one (code : InstructionAt program index instruction)
    (location : initial.status = .running index) :
    execute program 1 initial = stepOp instruction initial := by
  change step program initial = stepOp instruction initial
  simp only [step, location]
  cases entry : program[index]? with
  | none => simp [InstructionAt, entry] at code
  | some found => simp [InstructionAt, entry] at code; simp [code]

-- Every instruction has the same contract shape as a multi-instruction block.
-- `code` is checked automatically for concrete programs, or supplied explicitly.
theorem clear (program : Program) (index : Nat) (destination : Reg32) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.xor destination destination) := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial.write destination.parent 0 with
      status := .running (index+1), zeroFlag := true }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, put] <;> try rfl

theorem test_zero (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.test register register) := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial with
      status := .running (index+1), zeroFlag := initial.registers register == 0 }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp, next]

theorem read_byte (program : Program) (index : Nat) (destination : Reg32) (base : Reg) (initial : MachineState)
    (location : initial.status = .running index) (bound : initial.registers base < word)
    (allowed : initial.readable (initial.registers base) = true)
    (code : InstructionAt program index (.movzx destination (.bytePtr base)) := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial.write destination.parent (initial.memory (initial.registers base)).val with
      status := .running (index+1), readHistory := initial.readHistory ++ [⟨initial.registers base,1⟩] }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  have byteFitsWord (byte : Fin 256) : byte.val % word = byte.val := by
    apply Nat.mod_eq_of_lt
    have := byte.isLt
    unfold word
    omega
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, put] <;> try rfl

theorem add (program : Program) (index : Nat) (destination source : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.add destination source) := by decide +kernel) :
    let result := (initial.registers destination + initial.registers source) % word
    Ensures program 1 (· = initial) (· = { initial.write destination result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, put] <;> try rfl

theorem inc (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.inc register) := by decide +kernel) :
    let result := (initial.registers register + 1) % word
    Ensures program 1 (· = initial) (· = { initial.write register result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, put] <;> try rfl

theorem dec (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.dec register) := by decide +kernel) :
    let result := (word - 1 + initial.registers register) % word
    Ensures program 1 (· = initial) (· = { initial.write register result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, put] <;> try rfl

theorem branch_zero (program : Program) (index target : Nat) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.jz target) := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial with status := .running (if initial.zeroFlag then target else index+1) }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp]
  split <;> rfl

theorem branch_nonzero (program : Program) (index target : Nat) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.jnz target) := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial with status := .running (if initial.zeroFlag then index+1 else target) }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp]
  split <;> rfl

theorem return_ (program : Program) (index : Nat) (initial : MachineState)
    (location : initial.status = .running index) (slot : initial.ValidReturnSlot)
    (code : InstructionAt program index .ret := by decide +kernel) :
    Ensures program 1 (· = initial) (· = { initial.write .rsp ((initial.registers .rsp+8)%word) with
      status := .returned initial.returnAddress, readHistory := initial.readHistory ++ [⟨initial.registers .rsp,8⟩] }) := by
  constructor
  intro actual equal
  subst actual
  rw [one code location]
  simp_all [MachineState.write, MachineState.ValidReturnSlot, MachineState.returnAddress, stepOp, put, read64]
end Rivet
