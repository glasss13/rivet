module
public import Rivet.Model
import Rivet.ExecutionProperties
@[expose] public section
namespace Rivet

/-- Some finite execution reaches the final state. This alone does not guarantee
termination or correctness for every choice of undefined flags. -/
def Reaches (program : Program) (initial final : MachineState) : Prop :=
  ∃ (choices : FlagChoices) (steps : Nat), execute program steps initial choices = final

/-- Use a finite prefix of one supply, then continue with another. -/
private def appendChoices (choices : FlagChoices) (count : Nat) (rest : FlagChoices) : FlagChoices :=
  fun index => if index < count then choices index else rest (index - count)

@[simp] private theorem drop_appendChoices (choices rest : FlagChoices) (count : Nat) :
    (appendChoices choices count rest).drop count = rest := by
  funext index
  simp [FlagChoices.drop, appendChoices, Nat.not_lt_of_ge (Nat.le_add_right count index)]

/-- Bounded execution only depends on the corresponding finite prefix of choices. -/
private theorem execute_congr_choices (program : Program) (steps : Nat) (state : MachineState)
    (first second : FlagChoices) (agree : ∀ index < steps, first index = second index) :
    execute program steps state first = execute program steps state second := by
  induction steps generalizing state first second with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [execute, agree 0 (Nat.zero_lt_succ _)]
    apply inductionHypothesis
    intro index bound
    exact agree (1 + index) (by omega)

@[simp] private theorem execute_appendChoices (program : Program) (steps : Nat) (state : MachineState)
    (choices rest : FlagChoices) :
    execute program steps state (appendChoices choices steps rest) = execute program steps state choices := by
  apply execute_congr_choices
  intro index bound
  simp [appendChoices, bound]

theorem Reaches.trans (first : Reaches program initial intermediate)
    (second : Reaches program intermediate final) : Reaches program initial final := by
  obtain ⟨choices, earlier, rfl⟩ := first
  obtain ⟨rest, later, rfl⟩ := second
  exact ⟨appendChoices choices earlier rest, earlier + later, by simp [execute_add]⟩

/-- For every choice supply, a block eventually satisfies its postcondition.
The witness may depend on the supply; no instruction budget is required of callers. -/
structure Ensures (program : Program) (precondition postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ initial, precondition initial → ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute program steps initial choices = final) ∧ postcondition final

/-- Obtain one reachable result. The contract itself guarantees the postcondition
for every choice supply; this theorem does not expose that implementation detail. -/
theorem Ensures.run (contract : Ensures program precondition postcondition)
    (initial : MachineState) (assumption : precondition initial) :
    ∃ final, Reaches program initial final ∧ postcondition final := by
  let choices : FlagChoices := fun _ => ⟨false, false⟩
  obtain ⟨final, reached, result⟩ := contract.allChoices initial assumption choices
  exact ⟨final, ⟨choices, reached⟩, result⟩

/-- Prove a contract separately for each initial state satisfying the precondition. -/
theorem Ensures.intro
    (body : ∀ initial, precondition initial → Ensures program (· = initial) postcondition) :
    Ensures program precondition postcondition :=
  ⟨fun initial assumption => (body initial assumption).allChoices initial rfl⟩

/-- Establish a contract by one instruction, for every permitted undefined flag value.
Instruction rules use this when the model has no more specific rule yet. -/
theorem Ensures.of_step
    (transition : ∀ initial, precondition initial → ∀ undefinedFlags,
      postcondition (step program initial undefinedFlags)) :
    Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  exact ⟨step program initial (choices 0), ⟨1, rfl⟩, transition initial assumption (choices 0)⟩

/-- Retain reachability alongside a block's result, for deriving facts about the
initial/final state pair without opening the execution witness. -/
theorem Ensures.with_reachability (contract : Ensures program (· = initial) postcondition) :
    Ensures program (· = initial) (fun final => Reaches program initial final ∧ postcondition final) := by
  constructor
  intro actual equal choices
  subst actual
  obtain ⟨final, reached, result⟩ := contract.allChoices initial rfl choices
  exact ⟨final, reached, ⟨choices, reached⟩, result⟩

theorem Ensures.refl : Ensures program predicate predicate :=
  ⟨fun initial assumption _ => ⟨initial, ⟨0, rfl⟩, assumption⟩⟩

theorem Ensures.seq (first : Ensures program precondition intermediate)
    (second : Ensures program intermediate postcondition) : Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨middle, ⟨earlier, rfl⟩, holds⟩ := first.allChoices initial assumption choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := second.allChoices _ holds (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Ensures.consequence (contract : Ensures program precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures program strongerPrecondition weakerPostcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨final, reached, result⟩ := contract.allChoices initial (strengthenPrecondition _ assumption) choices
  exact ⟨final, reached, weakenPostcondition _ result⟩

/-- Iterate blocks while a natural-valued measure decreases. No instruction counts enter the rule. -/
theorem Ensures.loop (invariant finished : MachineState → Prop) (measure : MachineState → Nat)
    (body : ∀ initial, invariant initial → ¬ finished initial →
      Ensures program (· = initial) (fun final => invariant final ∧ measure final < measure initial)) :
    Ensures program invariant (fun final => invariant final ∧ finished final) := by
  constructor
  intro initial assumption choices
  induction bound : measure initial using Nat.strongRecOn generalizing initial choices with
  | ind bound inductionHypothesis =>
    by_cases done : finished initial
    · exact ⟨initial, ⟨0, rfl⟩, assumption, done⟩
    · obtain ⟨middle, ⟨earlier, rfl⟩, holds, decreases⟩ := (body initial assumption done).allChoices initial rfl choices
      obtain ⟨final, ⟨later, reached⟩, result⟩ := inductionHypothesis _ (by omega) _ holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Reaches.stopped (reached : Reaches program initial final)
    (stopped : initial.status.isRunning = false) : final = initial := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_stopped _ _ _ stopped

theorem Reaches.not_fault (reached : Reaches program initial final)
    (notFaulted : final.status ≠ .fault) : initial.status ≠ .fault := by
  intro faulted
  have equal := reached.stopped (by simp [faulted, ExecutionStatus.isRunning])
  subst final
  exact notFaulted faulted

theorem Reaches.reads_mono (reached : Reaches program initial final)
    (recorded : access ∈ initial.readHistory) : access ∈ final.readHistory := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_reads_monotone _ _ steps _ recorded

theorem Reaches.preserves_register (reached : Reaches program initial final) (register : Reg)
    (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    final.registers register = initial.registers register := by
  obtain ⟨choices, steps, rfl⟩ := reached
  apply execute_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

end Rivet
