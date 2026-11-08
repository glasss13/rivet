module
public import Rivet.Model
@[expose] public section
namespace Rivet

theorem execute_stopped (program : Program) (steps : Nat) (state : MachineState) {choices : FlagChoices} (stopped : state.status.isRunning = false) :
    execute program steps state choices = state := by
  have stepUnchanged (undefinedFlags : FlagValues) : step program state undefinedFlags = state := by
    cases status : state.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction steps generalizing choices with
  | zero => rfl
  | succ steps inductionHypothesis => simpa [execute, stepUnchanged] using inductionHypothesis (choices := choices.drop 1)

end Rivet
