module
public import Rivet.Tactics.ReadBack
public meta import Lean
-- `rivet_call block args (name := proof)* (as q)?`: runs the block from the current state and goes on
-- from the state it ends in, with what it left alone and its postcondition in scope, read back to the
-- block's start as a step's facts are. A precondition left out is proved as `rivet_known` does, with no
-- arithmetic; one that is not is an error naming it.
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

syntax (name := rivetCall) "rivet_call " term:max (ppSpace colGt (Lean.Parser.Term.namedArgument <|> term:max))*
  (" as " ident)? : tactic

@[tactic rivetCall] meta partial def evalRivetCall : Tactic := fun stx => withMainContext <| reporting m!"rivet_call" do
  let main ← getMainGoal
  let pending := (← getGoals).tail
  let goalArgs := (← whnfR (← main.getType)).getAppArgs
  let positional := stx[2].getArgs.filter (·.getKind != ``Lean.Parser.Term.namedArgument)
  let named := stx[2].getArgs.filter (·.getKind == ``Lean.Parser.Term.namedArgument)
  let head : TSyntax `term := ⟨stx[1]⟩
  let applied ← if positional.isEmpty then pure head else `($head $(positional.map (⟨·⟩))*)
  let given ← Tactic.elabTerm applied none (mayPostpone := true)
  let type ← whnfR (← inferType given)
  let names := type.getForallBinderNames.toArray
  let (holes, _, result) ← forallMetaTelescopeReducing type
  let result ← whnfR result
  unless result.isAppOfArity ``Block 5 do throwError "rivet_call: not a block:{indentExpr result}"
  unless (← isDefEq (result.getArg! 4) goalArgs[4]!) && (← isDefEq (result.getArg! 0) goalArgs[0]!) do
    throwError "rivet_call: the block{indentExpr result}\ndoes not start at the current state `{goalArgs[4]!}` \
      of this image"
  for argument in named do
    let name := argument[1].getId
    let some index := names.idxOf? name | throwError "rivet_call: the block has no argument `{name}`"
    let hole := holes[index]!.mvarId!
    hole.assign (← Tactic.elabTermEnsuringType argument[3] (← hole.getType))
  for (hole, name) in holes.zip names do
    let goal := hole.mvarId!
    if ← goal.isAssigned then continue
    unless ← isProp (← goal.getType) do throwError "rivet_call: give the block its argument `{name}`"
    try
      discard <| Tactic.run goal do evalTactic (← `(tactic| rivet_known))
    catch error =>
      throwError "rivet_call: the block's precondition `{name}` is not proved. Give it: `({name} := …)`.\n\
        {error.toMessageData}"
  let name (suffix : String) : TacticM Name :=
    if stx[3].getNumArgs > 0 then pure (stx[3][1].getId.appendAfter suffix)
    else mkFreshUserName (if suffix.isEmpty then `s else `h)
  let call ← instantiateMVars (mkAppN given holes)
  let args := (← whnfR (← inferType call)).getAppArgs
  let postName ← name "_post"
  let rest ← main.withContext do
    withLocalDeclD (← name "") (mkConst ``MachineState) fun next => do
    withLocalDeclD (← name "_kept") (mkApp3 (mkConst ``MachineState.Except) next args[1]! args[2]!) fun kept => do
    withLocalDeclD postName (args[3]!.beta #[next]) fun post => do
      let target := mkApp5 (mkConst ``Block) goalArgs[0]! goalArgs[1]! goalArgs[2]! goalArgs[3]! next
      let rest ← mkFreshExprSyntheticOpaqueMVar target (← main.getTag)
      main.assign (← mkAppM ``Block.then #[call, ← mkLambdaFVars #[next, kept, post] rest])
      (← ways rest.mvarId! post.fvarId! postName).mapM fun (goal, post) => do
        -- The postcondition read back once, now, as a step's facts are when it ends.
        let (goal, post) ← readBack goal post
        goal.withContext do
          -- Each part that says what a field of the new state is, on its own, as a step's facts are: all but
          -- a register the change does not list, which reads back as it was.
          let changed ← ReadBack.changedRegisters args[2]!
          let mut goal := goal
          for (proof, part) in ← ReadBack.parts (.fvar post) (← post.getType) do
            let some (_, lhs, _) := part.eq? | continue
            unless ReadBack.fieldOf? lhs == some next.fvarId! do continue
            if lhs.getAppNumArgs == 2 && !((← whnfR (lhs.getArg! 1)).constName?.any changed.contains) then continue
            goal := (← (← goal.assert (← ReadBack.noteName) part proof).intro1P).2
          return goal
  setGoals (rest.toList ++ pending)
where
  readBack (goal : MVarId) (post : FVarId) : TacticM (MVarId × FVarId) := goal.withContext do
    let type ← instantiateMVars (← post.getType)
    let facts := (← ReadBack.stepFacts).filter (· != .fvar post)
    let all ← ReadBack.lemmas (← ReadBack.opened type) facts #[
      ← `(Lean.Parser.Tactic.simpLemma| rivet), ← `(Lean.Parser.Tactic.simpLemma| ReadBack.placedRead)]
    setGoals [goal]
    let { ctx, simprocs, .. } ← mkSimpContext (← `(tactic| simp only [$all,*])) (eraseLocal := false)
    let (result, _) ← simp type ctx simprocs
    if result.expr == type then return (goal, post)
    let proof ← match result.proof? with
      | some equal => mkEqMP equal (.fvar post)
      | none => mkExpectedTypeHint (.fvar post) result.expr
    let replaced ← goal.replace post proof result.expr
    return (replaced.mvarId, replaced.fvarId)
  -- A postcondition that is an `∨` is one way out per side: a goal for each.
  ways (goal : MVarId) (post : FVarId) (name : Name) : MetaM (Array (MVarId × FVarId)) := goal.withContext do
    let type ← whnfR (← instantiateMVars (← post.getType))
    unless type.isAppOfArity ``Or 2 do return #[(goal, post)]
    let goal ← goal.replaceLocalDeclDefEq post type
    (← goal.cases post #[{ varNames := [name] }, { varNames := [name] }]).flatMapM fun case =>
      ways case.mvarId case.fields[0]!.fvarId! name

end Rivet.Internal
