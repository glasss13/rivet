module
public import Rivet.Model
import Rivet.Safety
@[expose] public section
namespace Rivet

abbrev InstructionAt (program : Program) (index : Nat) (instruction : Op) : Prop :=
  (program[index]?).map Instruction.op = some instruction

@[simp] theorem execute_zero (program : Program) (initial : MachineState) :
    execute program 0 initial = initial := by rfl

theorem execute_execute (program : Program) (later earlier : Nat) (initial : MachineState) :
    execute program later (execute program earlier initial) =
      execute program (earlier + later) initial := (execute_add program earlier later initial).symm

@[simp] theorem execute_returned (program : Program) (steps : Nat) (initial : MachineState)
    (returned : initial.status = .returned address) : execute program steps initial = initial :=
  execute_stopped program steps initial (by simp [returned, ExecutionStatus.isRunning])

@[simp] theorem execute_fault (program : Program) (steps : Nat) (initial : MachineState)
    (faulted : initial.status = .fault) : execute program steps initial = initial :=
  execute_stopped program steps initial (by simp [faulted, ExecutionStatus.isRunning])

theorem execute_reads_mono (program : Program) (steps : Nat) (initial : MachineState) (access : Access)
    (recorded : access ∈ initial.readHistory) : access ∈ (execute program steps initial).readHistory :=
  execute_reads_monotone program initial steps access recorded

theorem execute_preserves_register (program : Program) (steps : Nat) (initial : MachineState)
    (register : Reg) (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    (execute program steps initial).registers register = initial.registers register := by
  apply execute_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

/-- Finite reachability using the executable transition, including zero steps. -/
def Reaches (program : Program) (initial final : MachineState) : Prop :=
  ∃ steps, execute program steps initial = final

theorem Reaches.refl : Reaches program state state := ⟨0, rfl⟩

theorem Reaches.trans (first : Reaches program initial intermediate)
    (second : Reaches program intermediate final) : Reaches program initial final := by
  obtain ⟨earlier, rfl⟩ := first
  obtain ⟨later, rfl⟩ := second
  exact ⟨earlier + later, (execute_execute _ _ _ _).symm⟩

/-- A block eventually reaches a state satisfying its postcondition. -/
structure Ensures (program : Program) (precondition postcondition : MachineState → Prop) : Prop where
  run : ∀ initial, precondition initial → ∃ final, Reaches program initial final ∧ postcondition final

theorem Ensures.refl : Ensures program predicate predicate :=
  ⟨fun initial assumption => ⟨initial, Reaches.refl, assumption⟩⟩

theorem Ensures.seq (first : Ensures program precondition intermediate)
    (second : Ensures program intermediate postcondition) : Ensures program precondition postcondition := by
  constructor
  intro initial assumption
  obtain ⟨middle, reached, holds⟩ := first.run initial assumption
  obtain ⟨final, finished, result⟩ := second.run middle holds
  exact ⟨final, reached.trans finished, result⟩

theorem Ensures.consequence (contract : Ensures program precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures program strongerPrecondition weakerPostcondition := by
  constructor
  intro initial assumption
  obtain ⟨final, reached, result⟩ := contract.run initial (strengthenPrecondition _ assumption)
  exact ⟨final, reached, weakenPostcondition _ result⟩

/-- Successful function execution; return is required independently of the postcondition. -/
def Returns (program : Program) (precondition postcondition : MachineState → Prop) : Prop :=
  Ensures program precondition (fun final => (∃ address, final.status = .returned address) ∧ postcondition final)

theorem Ensures.returns (contract : Ensures program precondition postcondition)
    (returned : ∀ final, postcondition final → ∃ address, final.status = .returned address) :
    Returns program precondition postcondition :=
  contract.consequence (fun _ assumption => assumption) (fun final result => ⟨returned final result, result⟩)

/-- Iterate blocks while a natural-valued measure decreases. No instruction counts enter the rule. -/
theorem Ensures.loop (invariant finished : MachineState → Prop) (measure : MachineState → Nat)
    (body : ∀ initial, invariant initial → ¬ finished initial →
      Ensures program (· = initial) (fun final => invariant final ∧ measure final < measure initial)) :
    Ensures program invariant (fun final => invariant final ∧ finished final) := by
  constructor
  intro initial assumption
  induction bound : measure initial using Nat.strongRecOn generalizing initial with
  | ind bound inductionHypothesis =>
    by_cases done : finished initial
    · exact ⟨initial, Reaches.refl, assumption, done⟩
    · obtain ⟨middle, reached, holds, decreases⟩ := (body initial assumption done).run initial rfl
      obtain ⟨final, rest, result⟩ := inductionHypothesis (measure middle) (by omega) middle holds rfl
      exact ⟨final, reached.trans rest, result⟩

/-- A property holds at every finite reachable state. -/
def Always (program : Program) (initial : MachineState) (property : MachineState → Prop) : Prop :=
  ∀ final, Reaches program initial final → property final

theorem Always.induction (initially : property initial)
    (preserved : ∀ state, property state → property (step program state)) : Always program initial property := by
  intro final ⟨steps, equal⟩
  subst final
  induction steps generalizing initial with
  | zero => exact initially
  | succ steps inductionHypothesis => exact inductionHypothesis (preserved initial initially)

/-- Every finite prefix is still running. Stopped-state stuttering does not qualify. -/
def Diverges (program : Program) (initial : MachineState) : Prop :=
  Always program initial (fun state => state.status.isRunning = true)

theorem Reaches.stopped (reached : Reaches program initial final)
    (stopped : initial.status.isRunning = false) : final = initial := by
  obtain ⟨steps, rfl⟩ := reached
  exact execute_stopped _ _ _ stopped

/-- Determinism orders any two reachable states along the same execution. -/
theorem Reaches.comparable (first : Reaches program initial left)
    (second : Reaches program initial right) : Reaches program left right ∨ Reaches program right left := by
  obtain ⟨earlier, rfl⟩ := first
  obtain ⟨later, rfl⟩ := second
  by_cases order : earlier ≤ later
  · left; exact ⟨later-earlier, by rw [execute_execute]; congr 1; omega⟩
  · right; exact ⟨earlier-later, by rw [execute_execute]; congr 1; omega⟩

/-- Every reachable state can still reach an eventual successful return. -/
theorem Reaches.to_return (terminal : Reaches program initial final)
    (returned : final.status = .returned address) (reachable : Reaches program initial state) :
    Reaches program state final := by
  rcases reachable.comparable terminal with before | after
  · exact before
  · have equal := after.stopped (by simp [returned, ExecutionStatus.isRunning])
    subst state
    exact Reaches.refl

theorem Reaches.not_fault (reached : Reaches program initial final)
    (returned : final.status = .returned address) : initial.status ≠ .fault := by
  intro faulted
  have equal := reached.stopped (by simp [faulted, ExecutionStatus.isRunning])
  subst final
  simp [faulted] at returned

/-- Successful eventual return rules out faults at every reachable state. -/
theorem Returns.never_faults (contract : Returns program precondition postcondition)
    (initially : precondition initial) :
    Always program initial (fun state => state.status ≠ .fault) := by
  obtain ⟨final, terminal, ⟨address, returned⟩, _⟩ := contract.run initial initially
  intro state reachable
  exact (terminal.to_return returned reachable).not_fault returned

theorem Reaches.reads_mono (reached : Reaches program initial final)
    (recorded : access ∈ initial.readHistory) : access ∈ final.readHistory := by
  obtain ⟨steps, rfl⟩ := reached
  exact execute_reads_mono _ steps _ _ recorded

theorem Reaches.preserves_register (reached : Reaches program initial final) (register : Reg)
    (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    final.registers register = initial.registers register := by
  obtain ⟨steps, rfl⟩ := reached
  exact execute_preserves_register _ steps _ register unchanged

/-- Positive progress through running checkpoints proves indefinite execution. -/
theorem Diverges.of_progress (invariant : MachineState → Prop) (initially : invariant initial)
    (progress : ∀ state, invariant state → state.status.isRunning = true ∧
      ∃ nextState, Reaches program (step program state) nextState ∧ invariant nextState) :
    Diverges program initial := by
  intro final ⟨steps, equal⟩
  subst final
  induction steps using Nat.strongRecOn generalizing initial with
  | ind steps inductionHypothesis =>
    obtain ⟨running, nextState, ⟨remainingSteps, rfl⟩, nextInvariant⟩ := progress initial initially
    let length := remainingSteps + 1
    have positive : 0 < length := Nat.zero_lt_succ _
    change invariant (execute program length initial) at nextInvariant
    by_cases order : length ≤ steps
    · have rest := inductionHypothesis (steps-length) (by omega) nextInvariant
      simpa [execute_execute, Nat.add_sub_of_le order] using rest
    · cases stoppedBool : (execute program steps initial).status.isRunning with
      | true => rfl
      | false =>
        have unchanged := execute_stopped program (length-steps) (execute program steps initial) stoppedBool
        change execute program (length-steps) (execute program steps initial) = _ at unchanged
        rw [execute_execute, Nat.add_sub_of_le (by omega : steps ≤ length)] at unchanged
        have nextRunning := (progress _ nextInvariant).1
        rw [unchanged] at nextRunning
        simp [stoppedBool] at nextRunning

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
    Ensures program (· = initial) (· = { initial.write destination.parent 0 with
      status := .running (index+1), zeroFlag := true }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem test_zero (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.test register register) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (index+1), zeroFlag := initial.registers register == 0 }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp, next]

theorem read_byte (program : Program) (index : Nat) (destination : Reg32) (base : Reg) (initial : MachineState)
    (location : initial.status = .running index) (allowed : initial.readable (initial.registers base).toNat = true)
    (code : InstructionAt program index (.movzx destination (.bytePtr base)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination.parent (BitVec.ofNat 64 (initial.memory (initial.registers base).toNat).val) with
      status := .running (index+1), readHistory := initial.readHistory ++ [⟨(initial.registers base).toNat,1⟩] }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem add (program : Program) (index : Nat) (destination source : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.add destination source) := by decide +kernel) :
    let result := initial.registers destination + initial.registers source
    Ensures program (· = initial) (· = { initial.write destination result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem inc (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.inc register) := by decide +kernel) :
    let result := initial.registers register + 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem dec (program : Program) (index : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.dec register) := by decide +kernel) :
    let result := initial.registers register - 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (index+1), zeroFlag := result == 0 }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem branch_zero (program : Program) (index target : Nat) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.jz target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then target else index+1) }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp]
  split <;> rfl

theorem branch_nonzero (program : Program) (index target : Nat) (initial : MachineState)
    (location : initial.status = .running index := by rfl)
    (code : InstructionAt program index (.jnz target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then index+1 else target) }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [ExecutionStatus.advance, stepOp]
  split <;> rfl

theorem return_ (program : Program) (index : Nat) (initial : MachineState)
    (location : initial.status = .running index) (slot : initial.ValidReturnSlot)
    (code : InstructionAt program index .ret := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write .rsp (initial.registers .rsp + 8) with
      status := .returned initial.returnAddress, readHistory := initial.readHistory ++ [⟨(initial.registers .rsp).toNat,8⟩] }) := by
  constructor
  intro actual equal
  subst actual
  refine ⟨execute program 1 initial, ⟨1, rfl⟩, ?_⟩
  rw [one code location]
  simp_all [MachineState.write, MachineState.ValidReturnSlot, MachineState.returnAddress, stepOp, read64]
end Rivet
