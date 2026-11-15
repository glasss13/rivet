module
public import Rivet.Tactics.Registers
-- `rivet_arith (only)? [facts]`: proves an arithmetic goal about words and numbers with `lia`, within
-- a fixed budget that `maxHeartbeats` does not change. The registers of the goal and of the facts it
-- uses are read back to the block's start first. General (`∀`) facts in scope are hidden, and with
-- `only`, every other hypothesis.
public meta import Lean
public section
namespace Rivet
open Lean Meta Elab Tactic

meta def arithBudget : Nat := 20000

-- `lia`'s report without `grind`'s restatements of the goal's facts (asserted facts, equivalence
-- classes): on a large context they are nearly all of it.
meta partial def withoutRestatements : MessageData → MessageData
  | .trace data header children =>
    .trace data header <| (children.filter fun
      | .trace part _ _ => part.cls != `facts && part.cls != `eqc
      | _ => true).map withoutRestatements
  | .withContext context message => .withContext context (withoutRestatements message)
  | .withNamingContext naming message => .withNamingContext naming (withoutRestatements message)
  | .nest indent message => .nest indent (withoutRestatements message)
  | .group message => .group (withoutRestatements message)
  | .compose first second => .compose (withoutRestatements first) (withoutRestatements second)
  | .tagged tag message => .tagged tag (withoutRestatements message)
  | message => message

syntax (name := rivetArith) "rivet_arith" (&" only")? (" [" term,* "]")? : tactic

@[tactic rivetArith] meta def evalRivetArith : Tactic := fun stx => withMainContext do
  let only := !stx[1].isNone
  let facts := if stx[2].isNone then #[] else stx[2][1].getSepArgs
  let others := (← getGoals).tail
  let mut goal ← getMainGoal
  let unlisted ← if only then goal.withContext do
      (← getLCtx).foldlM (init := #[]) fun unlisted decl => do
        if decl.isImplementationDetail then return unlisted
        return if ← isProp decl.type then unlisted.push decl.fvarId else unlisted
    else pure #[]
  let mut given := #[]
  for term in facts do
    let proof ← instantiateMVars (← Tactic.elabTerm term none)
    let type ← inferType proof
    -- `lia` does not instantiate a general statement, so one would be silently unused.
    if let .forallE _ domain _ _ ← whnfR type then
      unless ← isProp domain do
        throwError "rivet_arith: the fact `{term}` is general: `{type}`. `lia` uses only facts about \
          the goal's terms; give it its arguments."
    for (part, partType) in ← ReadBack.parts proof type do
      let (fact, next) ← (← goal.assert (← mkFreshUserName `fact) partType part).intro1P
      given := given.push fact
      goal := next
  -- The goal and the facts it may use, with their registers read back, so they meet.
  setGoals [goal]
  let moved ← goal.withContext do
    let later ← ReadBack.later
    let used ← if only then given.mapM (·.getDecl) else ReadBack.hypotheses
    let moved ← used.filterM fun decl => return later.any ((← instantiateMVars decl.type).containsFVar ·)
    let target ← instantiateMVars (← goal.getType)
    if moved.isEmpty && !later.any (target.containsFVar ·) then pure none else
      some <$> ReadBack.registersBack target (← moved.mapM fun decl => Term.exprToSyntax decl.toExpr)
  if let some readBack := moved then
    evalTactic (← `(tactic| try $readBack:tactic))
    let [read] ← getGoals | setGoals others; return
    goal := read
  -- `lia` never instantiates a general fact, but `grind` still prepares each one, within the budget.
  let hidden ← goal.withContext do
    (← getLCtx).foldlM (init := #[]) fun hidden decl => do
      if decl.isImplementationDetail then return hidden
      if unlisted.contains decl.fvarId then return hidden.push decl.fvarId
      let .forallE _ domain _ _ ← whnfR (← instantiateMVars decl.type) | return hidden
      return if (← isProp decl.type) && !(← isProp domain) then hidden.push decl.fvarId else hidden
  for fact in hidden.reverse do
    goal ← goal.tryClear fact
  setGoals [goal]
  let start ← IO.getNumHeartbeats
  let attempt := withTheReader Core.Context
    (fun context => { context with initHeartbeats := start, maxHeartbeats := arithBudget * 1000 })
    (evalTactic (← `(tactic| lia)))
  try
    tryCatchRuntimeEx attempt fun error => do
      -- Its budget is its own; Lean's recursion limit is not, and stops the tactic.
      if error.isMaxRecDepth then throw error
      -- `grind` reports its own timeout as an ordinary failure, so compare the work done.
      if error.isMaxHeartbeat || (← IO.getNumHeartbeats) - start ≥ arithBudget * 1000 then
        throwError "rivet_arith: no proof within its budget of {arithBudget} heartbeats; \
          `maxHeartbeats` does not change it. Give it only the facts the goal needs: \
          `rivet_arith only [facts]`."
      throwError "rivet_arith: `lia` did not prove the goal from the facts in scope. Below is where it \
        stopped. Its assignment may or may not be a counterexample: `lia` drops what it does not read, \
        and may stop before it has tried everything.\n\
        - Facts the goal does not need, such as `%` or `/` facts and large `∨`s, can keep `lia` from a \
        proof: give it only those it needs, `rivet_arith only [facts]`.\n\
        - A term `lia` does not read, such as a mask, needs its meaning as an equation, e.g. \
        `x &&& 15#64 = x % 16#64`, proved through `toNat`.\n\
        - A goal that adds or subtracts a shifted value may need `grind`.\n\
        - `lia` does not unfold definitions: unfold them, or list facts about them.\
        {indentD (withoutRestatements error.toMessageData)}"
  finally
    IO.setNumHeartbeats start
  setGoals others

end Rivet
