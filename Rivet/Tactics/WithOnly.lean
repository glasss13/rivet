module
-- `with_only [facts] => tac`: runs a tactic on the goal with only the listed facts in scope.
public meta import Lean
public section
namespace Rivet
open Lean Meta Elab Tactic

syntax (name := withOnly) "with_only" " [" term,* "]" " => " tacticSeq : tactic

@[tactic withOnly] meta def evalWithOnly : Tactic := fun stx => withMainContext do
  let facts ← stx[2].getSepArgs.mapM fun term => do
    let proof ← instantiateMVars (← Tactic.elabTerm term none)
    let name ← match term with
      | `($name:ident) => pure (Name.mkSimple name.getId.getString!)
      | _ => mkFreshUserName `fact
    return (name, proof, ← inferType proof)
  let mut goal ← getMainGoal
  let hidden ← goal.withContext do
    (← getLCtx).foldlM (init := #[]) fun hidden decl => do
      if decl.isImplementationDetail then return hidden
      return if ← isProp decl.type then hidden.push decl.fvarId else hidden
  for (name, proof, type) in facts do
    goal := (← (← goal.assert name type proof).intro1P).2
  for fact in hidden.reverse do
    goal ← goal.tryClear fact
  setGoals [goal]
  Core.withCurrHeartbeats <| evalTactic stx[5]
  let remaining ← getGoals
  unless remaining.isEmpty do
    throwError "with_only: the tactic did not close the goal; it left{indentD (goalsToMessageData remaining)}"

end Rivet
