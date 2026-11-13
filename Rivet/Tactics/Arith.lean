module
-- `rivet_arith (only)? [facts]`: proves an arithmetic goal about words and numbers with `lia`, within
-- a fixed budget that `maxHeartbeats` does not change. With `only`, the other hypotheses are hidden.
public meta import Lean
public section
namespace Rivet
open Lean Meta Elab Tactic

meta def arithBudget : Nat := 20000

syntax (name := rivetArith) "rivet_arith" (&" only")? (" [" term,* "]")? : tactic

@[tactic rivetArith] meta def evalRivetArith : Tactic := fun stx => withMainContext do
  let only := !stx[1].isNone
  let facts := if stx[2].isNone then #[] else stx[2][1].getSepArgs
  let mut goal ← getMainGoal
  let others := (← getGoals).tail
  let hidden ← if only then goal.withContext do
      (← getLCtx).foldlM (init := #[]) fun hidden decl => do
        if decl.isImplementationDetail then return hidden
        return if ← isProp decl.type then hidden.push decl.fvarId else hidden
    else pure #[]
  for term in facts do
    let proof ← instantiateMVars (← Tactic.elabTerm term none)
    let type ← inferType proof
    -- `lia` does not instantiate a general statement, so one would be silently unused.
    if let .forallE _ domain _ _ ← whnfR type then
      unless ← isProp domain do
        throwError "rivet_arith: the fact `{term}` is general: `{type}`. `lia` uses only facts about \
          the goal's terms; give it its arguments."
    goal := (← (← goal.assert (← mkFreshUserName `fact) type proof).intro1P).2
  for fact in hidden.reverse do
    goal ← goal.tryClear fact
  setGoals [goal]
  let start ← IO.getNumHeartbeats
  let attempt := withTheReader Core.Context
    (fun context => { context with initHeartbeats := start, maxHeartbeats := arithBudget * 1000 })
    (evalTactic (← `(tactic| lia)))
  try
    tryCatchRuntimeEx attempt fun error => do
      -- `grind` reports its own timeout as an ordinary failure, so compare the work done.
      if error.isMaxHeartbeat || (← IO.getNumHeartbeats) - start ≥ arithBudget * 1000 then
        throwError "rivet_arith: no proof within its budget of {arithBudget} heartbeats; \
          `maxHeartbeats` does not change it. Give it only the facts the goal needs: \
          `rivet_arith only [facts]`."
      throwError "rivet_arith: `lia` did not prove the goal from the facts in scope. The goal is not \
        necessarily false: an assignment below satisfies what `lia` understood of it.\n\
        - A term `lia` does not read, such as a mask, needs its meaning as an equation, e.g. \
        `x &&& 15#64 = x % 16#64`, proved through `toNat`.\n\
        - A goal that adds or subtracts a shifted value may need `grind`.\n\
        - `lia` does not unfold definitions: unfold them, or list facts about them.\n\
        - A law's bound that fails by default can be given, or kept as a goal: `(fits := ?_)`.\
        {indentD error.toMessageData}"
  finally
    IO.setNumHeartbeats start
  setGoals others

end Rivet
