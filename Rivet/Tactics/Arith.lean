module
public import Rivet.Tactics.ReadBack
public meta import Lean
-- `rivet_arith [facts]`: proves an arithmetic goal about words and numbers with `lia` from the listed
-- facts alone, within a fixed budget that `maxHeartbeats` does not change. The goal and the facts are
-- read back to the block's start first, registers and memory.
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

syntax (name := rivetArith) "rivet_arith" (" [" term,* "]")? : tactic

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
  let terms := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let others := (← getGoals).tail
  let mut goal ← getMainGoal
  let unlisted ← goal.withContext do
    (← getLCtx).foldlM (init := #[]) fun unlisted decl => do
      if decl.isImplementationDetail then return unlisted
      return if ← isProp decl.type then unlisted.push decl.fvarId else unlisted
  let mut listed := #[]
  let mut given := #[]
  for term in terms do
    let proof ← instantiateMVars (← Tactic.elabTerm term none)
    listed := listed.push proof
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
  let used ← goal.withContext do given.mapM fun fact => Term.exprToSyntax (.fvar fact)
  evalTactic (← `(tactic| try $(← readBackTactic used (goal := true)):tactic))
  let [read] ← getGoals | close; setGoals others; return
  goal := read
  let readType ← goal.withContext do instantiateMVars (← goal.getType)
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
    (fun context => { context with
      initHeartbeats := start
      maxHeartbeats := arithBudget * 1000
      options := Elab.async.set (maxHeartbeats.set context.options arithBudget) false })
    (do evalTactic (← `(tactic| lia)); close)
  try
    tryCatchRuntimeEx attempt fun error => do
      -- Its budget is its own; Lean's recursion limit is not, and stops the tactic.
      if error.isMaxRecDepth then throw error
      -- `grind` reports its own timeout as an ordinary failure, so compare the work done.
      if error.isMaxHeartbeat || (← IO.getNumHeartbeats) - start ≥ arithBudget * 1000 then
        -- A product of two terms with variables, in the goal or a listed fact.
        let product ← goal.withContext do
          let types := (← getLCtx).foldl (init := #[readType]) fun types decl =>
            if decl.isImplementationDetail then types else types.push decl.type
          types.anyM fun type => return ((← instantiateMVars type).find? fun e =>
            e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 4).hasFVar && (e.getArg! 5).hasFVar).isSome
        let hint := if product then m!"\n- A product of two variables can make `lia`'s proof too costly to check: \
          name it first, `generalize x * y = p at *`." else m!""
        throwError "rivet_arith: no proof within its budget of {arithBudget} heartbeats; \
          `maxHeartbeats` does not change it.\n\
          - List only the facts the goal needs.{hint}"
      -- What you may have meant to list: hypotheses about the goal's variables, registers and reads.
      let unused : MessageData ← outer.withContext do
        let atoms := (← atomsOf outerType) ++ (← atomsOf readType)
        let related := (← facts outer).filter fun (proof, part) =>
          !proof.hasAnyFVar (fun fact => given.contains fact || listed.any (·.containsFVar fact)) &&
            atoms.any fun atom => (part.find? (· == atom)).isSome
        if related.isEmpty then return m!""
        addMessageContext m!"\n- Facts in scope about its terms, not listed: \
          {MessageData.joinSep (related.toList.map fun (proof, _) => m!"`{proof}`") ", "}."
      throwError "rivet_arith: `lia` did not prove the goal from the listed facts. Below is where it \
        stopped. Its assignment may or may not be a counterexample: `lia` drops what it does not read, \
        and may stop before it has tried everything.{unused}\n\
        - Facts the goal does not need, such as `%` or `/` facts and large `∨`s, can keep `lia` from a \
        proof: list only those it needs.\n\
        - A term `lia` does not read, such as a mask, needs its meaning as an equation, e.g. \
        `x &&& 15#64 = x % 16#64`, proved through `toNat`.\n\
        - `lia` does not unfold definitions: unfold them, or list facts about them.\
        {indentD (withoutRestatements error.toMessageData)}"
  finally
    IO.setNumHeartbeats start
  setGoals others

@[tactic rivetArith] meta def evalRivetArith : Tactic := arith

end ReadBack

end Rivet.Internal
