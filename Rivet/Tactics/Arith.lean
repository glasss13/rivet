module
public import Rivet.Tactics.ReadBack
public meta import Lean
-- `rivet_arith (only)? [facts]`: proves an arithmetic goal about words and numbers with `lia`, within
-- a fixed budget that `maxHeartbeats` does not change. The goal and the facts it uses are read back to
-- the block's start first, registers and memory. General (`∀`) facts in scope are hidden, and with
-- `only`, every other hypothesis.
public section
namespace Rivet
open Lean Meta Elab Tactic

syntax (name := rivetArith) "rivet_arith" (&" only")? (" [" term,* "]")? : tactic

namespace ReadBack

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

meta partial def arith (stx : Syntax) : TacticM Unit := withMainContext do
  -- A record is proved field by field, as a listed record is given field by field. `lia` reads `∧` itself.
  let record ← do
    let type ← whnfR (← instantiateMVars (← getMainTarget))
    let env ← getEnv
    pure (type.getAppFn.constName?.any fun name => name != ``And && isStructure env name)
  if record then
    let others := (← getGoals).tail
    for field in ← (← getMainGoal).constructor do
      setGoals [field]
      arith stx
    setGoals others
    return
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
    for (part, partType) in ← parts proof type do
      let (fact, next) ← (← goal.assert (← mkFreshUserName `fact) partType part).intro1P
      given := given.push fact
      goal := next
  -- Everything below works on a copy of the goal, and its proof is checked at once, as a lemma of its
  -- own, not at the end of your theorem.
  let outer := goal
  let outerType ← goal.withContext do instantiateMVars (← goal.getType)
  let copy ← goal.withContext do mkFreshExprSyntheticOpaqueMVar outerType
  let close : TacticM Unit := outer.withContext do
    outer.assign (← mkAuxTheorem outerType (← instantiateMVars copy))
  goal := copy.mvarId!
  -- The goal and the facts it may use, read back and in the `rivet` set's form, as every value Rivet
  -- writes is.
  setGoals [goal]
  let moved ← goal.withContext do
    let later ← later
    let used ← if only then given.mapM (·.getDecl) else hypotheses
    let moved ← used.filterM fun decl => return later.any ((← instantiateMVars decl.type).containsFVar ·)
    if moved.isEmpty && !later.any ((← instantiateMVars (← goal.getType)).containsFVar ·) then pure none else
      some <$> readBackTactic (← moved.mapM fun decl => Term.exprToSyntax decl.toExpr) (goal := true)
  if let some readBack := moved then
    evalTactic (← `(tactic| try $readBack:tactic))
  else
    let used ← goal.withContext do
      let used ← if only then given.mapM (·.getDecl) else hypotheses
      used.mapM fun decl => Term.exprToSyntax decl.toExpr
    evalTactic (← `(tactic| try simp only [rivet] at $[$used]* ⊢))
  let [read] ← getGoals | close; setGoals others; return
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
    tryCatchRuntimeEx (do attempt; close) fun error => do
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
        - `lia` does not unfold definitions: unfold them, or list facts about them.\
        {indentD (withoutRestatements error.toMessageData)}"
  finally
    IO.setNumHeartbeats start
  setGoals others

@[tactic rivetArith] meta def evalRivetArith : Tactic := arith

end ReadBack

end Rivet
