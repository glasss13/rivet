module
public import Rivet.Laws.Changes
public import Rivet.Laws.SimpSet
public meta import Lean
-- `rivet_changes`, and reads of unchanged registers in the `rivet` set.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace ChangesTactic

private meta partial def listItems (list : Expr) : MetaM (Array Expr) := do
  let list ← whnfD list
  if list.isAppOfArity ``List.nil 1 then return #[]
  if list.isAppOfArity ``List.cons 3 then return #[list.getArg! 1] ++ (← listItems (list.getArg! 2))
  throwError "rivet_changes: a change lists its registers and ranges one by one; this is not such a list:\
    {indentExpr list}"

private meta def changedRegisters (c : Expr) : MetaM (Array Name) := do
  (← listItems (mkApp (mkConst ``Changes.registers) c)).mapM fun register => do
    let some name := (← whnfD register).constName?
      | throwError "rivet_changes: a change names its registers; this is not a register name:\
          {indentExpr register}"
    return name

private meta def changedRanges (c : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  (← listItems (mkApp (mkConst ``Changes.memory) c)).mapM fun range => do
    let pair ← whnfD range
    unless pair.isAppOfArity ``Prod.mk 4 do
      throwError "rivet_changes: a change gives each range as `(low, high)`; this is not one:{indentExpr range}"
    return (pair, pair.getArg! 2, pair.getArg! 3)

private meta def showRange (low high : Expr) : MessageData := m!"[{low}, {high})"

private meta def prove (type : Expr) (tactic : TacticM (TSyntax `tactic)) : TacticM (Except Exception Expr) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let saved ← saveState
  try
    let remaining ← Tactic.run goal.mvarId! do evalTactic (← tactic)
    unless remaining.isEmpty do throwError "unsolved goals{indentD (goalsToMessageData remaining)}"
    return .ok (← instantiateMVars goal)
  catch error =>
    saved.restore
    return .error error

private meta def arith (type : Expr) (failure : MessageData) : TacticM Expr := do
  match ← prove type `(tactic| rivet_arith) with
  | .ok proof => return proof
  | .error error => throwError "rivet_changes: {failure}\n{error.toMessageData}"

-- `∀ x ∈ items, motive x`, from a proof of `motive x` for each item.
private meta def forEachItem (statement : Expr) (items : Array Expr)
    (item : Expr → Expr → TacticM Expr) : TacticM Expr := do
  let .forallE name domain (.forallE _ _ body _) _ := statement
    | throwError "rivet_changes: unexpected statement{indentExpr statement}"
  let motive := Expr.lam name domain (body.lowerLooseBVars 1 1) .default
  let mut proof ← mkAppOptM ``List.forall_mem_nil #[domain, motive]
  let mut rest ← mkListLit domain []
  for x in items.reverse do
    let head ← item x (motive.beta #[x])
    proof ← mkAppM ``Iff.mpr #[← mkAppOptM ``List.forall_mem_cons #[domain, motive, x, rest],
      ← mkAppM ``And.intro #[head, proof]]
    rest ← mkAppM ``List.cons #[x, rest]
  return proof

private meta def member (x : Expr) (items : Array Expr) : TacticM Expr := do
  let type ← mkAppM ``Membership.mem #[← mkListLit (← inferType x) items.toList, x]
  match ← prove type `(tactic| simp only [List.mem_cons, eq_self, true_or, or_true]) with
  | .ok proof => return proof
  | .error error => throwError "rivet_changes: {error.toMessageData}"

private meta def unfolded (type : Expr) : MetaM Expr := do
  let some type ← unfoldDefinition? type | throwError "rivet_changes: cannot unfold{indentExpr type}"
  return type.headBeta

private meta def outside (coll register : Expr) : TacticM Expr := do
  let some name := (← whnfD register).constName?
    | throwError "rivet_changes: this is not a register name:{indentExpr register}"
  if ← (← listItems coll).anyM fun other => return (← whnfD other).constName? == some name then
    throwError "rivet_changes: register `{register}` is in the change, so it may have changed."
  mkDecideProof (mkNot (← mkAppM ``Membership.mem #[coll, register]))

private meta def misses (c low high : Expr) (type : Expr) : TacticM Expr := do
  let ranges ← changedRanges c
  forEachItem (← unfolded type) (ranges.map (·.1)) fun pair _ => do
    let some (_, changedLow, changedHigh) := ranges.find? (·.1 == pair) | unreachable!
    arith (mkOr (← mkAppM ``LE.le #[high, changedLow]) (← mkAppM ``LE.le #[changedHigh, low]))
      m!"the range {showRange low high} is not shown to miss the changed range \
        {showRange changedLow changedHigh}."

-- The most recent fact `lhs = …` in scope.
private meta def factAbout (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut found := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, left, right) := (← instantiateMVars decl.type).eq? | continue
    if left == lhs then found := some (right, decl.toExpr)
  return found

-- Every `state.Except earlier c` in scope, newest first: the nested blocks that ended in `state`.
private meta def keptBy (state : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr MachineState.Except t earlier c := ← instantiateMVars decl.type | continue
    if t == state then found := found.push (earlier, c, decl.toExpr)
  return found.reverse

-- The value of a register in a state, followed through the steps' facts to the state they
-- start from: the value, whether a step wrote it, and a proof that the register holds it.
private meta partial def readRegister (state register : Expr) : MetaM (Expr × Bool × Expr) := do
  let read := mkApp2 (mkConst ``MachineState.registers) state register
  let some (function, fact) ← factAbout (mkApp (mkConst ``MachineState.registers) state)
    | let facts ← keptBy state
      if facts.isEmpty then return (read, false, ← mkEqRefl read)
      let some (earlier, c, kept) ← facts.findM? fun (_, c, _) =>
          return !(← changedRegisters c).contains register.constName!
        | return (read, true, ← mkEqRefl read)
      let out ← mkDecideProof (mkNot (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.registers) c, register]))
      let (earlierValue, written, rest) ← readRegister earlier register
      return (earlierValue, written,
        ← mkEqTrans (mkApp6 (mkConst ``MachineState.Except.sameRegisters) state earlier c kept register out) rest)
  let proof ← mkCongrFun fact register
  let mut value := (mkApp function register).headBeta
  repeat
    let_expr ite _ test _ written otherwise := value | break
    let_expr Eq _ _ other := test | break
    let some name := (← whnfR other).constName? | break
    if some name == register.constName? then return (written, true, proof)
    value := otherwise
  let_expr MachineState.registers earlier _ := value | return (value, true, proof)
  if earlier == state then return (value, false, proof)
  let (earlierValue, written, rest) ← readRegister earlier register
  return (earlierValue, written, ← mkEqTrans proof rest)

-- `t`'s register and `s`'s, each followed back to where the facts start, are the same there.
private meta def registerKept (t s c register : Expr) : TacticM Expr := do
  let goal ← mkEq (mkApp2 (mkConst ``MachineState.registers) t register)
    (mkApp2 (mkConst ``MachineState.registers) s register)
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← instantiateMVars decl.type) == goal then return decl.toExpr
  let (value, written, proof) ← readRegister t register
  let (start, startWritten, startProof) ← readRegister s register
  let back ← mkEqSymm startProof
  if ← withReducible <| isDefEq value start then return ← mkEqTrans proof back
  unless written || startWritten do
    throwError "rivet_changes: could not follow register `{register}` from{indentExpr t}\nand from\
      {indentExpr s}\nto the same value. The steps' facts give{indentExpr value}\nand{indentExpr start}"
  -- What memory holds: the stores, each state's memory, and reads that a nested block left alone.
  let mut definitions := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let lemma? ← if type.isAppOfArity ``MachineState.Except 3 then
        some <$> mkAppM ``MachineState.Except.readBytes #[decl.toExpr]
      else match type.eq? with
        | some (_, .fvar memory, _) =>
          pure <| if (← memory.getType).isConstOf ``Memory then some decl.toExpr else none
        | some (_, lhs, _) => pure <| if lhs.isAppOfArity ``MachineState.memory 1 then some decl.toExpr else none
        | none => pure none
    if let some lemma := lemma? then
      definitions := definitions.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax lemma):term))
  match ← prove (← mkEq value start) `(tactic| first
      | rfl
      | simp (disch := first | rivet_changes | rivet_arith) [$definitions,*, rivet,
          Memory.readBytes_storeBytes_inside, Memory.readBytes_storeBytes_outside]) with
  | .ok same => mkEqTrans proof (← mkEqTrans same back)
  | .error error =>
    let unnamed := if (← t.fvarId!.getUserName).hasMacroScopes then
      m!"\nName the last state (`rivet_step … as t`): its registers are then stated over the block's start." else m!""
    let writer ← match value.app2? ``MachineState.registers with
      | some (state, _) => pure <| if !(← keptBy state).isEmpty then
          m!"changed by the nested block ending in{indentExpr state}\nand" else m!"written, and"
      | none => pure m!"written, and"
    throwError "rivet_changes: register `{register}` is {writer} it is not in the change{indentExpr c}\n\
      Its value is{indentExpr value}\nand it is not shown to be{indentExpr start}\n\
      Reading it back, as for a register saved and restored, failed with{indentD error.toMessageData}{unnamed}"

-- `names` are what the facts say `s`'s memory is, each with a proof that it is.
private meta partial def memoryKept (names : Array (Expr × Expr)) (c address memory : Expr) : TacticM Expr := do
  if let some (_, same) := names.find? (·.1 == memory) then return ← mkCongrFun (← mkEqSymm same) address
  if memory.isAppOfArity ``Memory.storeBytes 4 then
    let #[earlier, base, length, bytes] := memory.getAppArgs | unreachable!
    let ranges ← changedRanges c
    let baseValue ← mkAppM ``BitVec.toNat #[base]
    let addressValue ← mkAppM ``BitVec.toNat #[address]
    let away ← arith (mkOr (← mkAppM ``LT.lt #[addressValue, baseValue])
        (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[baseValue, length], addressValue]))
      m!"the {length} bytes stored at{indentExpr base}\nare not shown to lie inside the change's \
        memory, {MessageData.joinSep (ranges.toList.map fun (_, low, high) => showRange low high) ", "}."
    return ← mkEqTrans (← mkAppOptM ``Memory.read_storeBytes_outside #[earlier, base, length, bytes, address, away])
      (← memoryKept names c address earlier)
  if let some (earlier, fact) ← factAbout memory then
    return ← mkEqTrans (← mkCongrFun fact address) (← memoryKept names c address earlier)
  let facts ← match memory.app1? ``MachineState.memory with
    | some state => keptBy state
    | none => pure #[]
  if facts.isEmpty then
    throwError "rivet_changes: nothing in scope says what this memory is, relative to{indentExpr names[0]!.1}\n\
      {indentExpr memory}"
  let low ← mkAppM ``BitVec.toNat #[address]
  let high ← mkAppM ``HAdd.hAdd #[low, mkNatLit 1]
  let mut failure := none
  for (earlier, inner, kept) in facts do
    match ← prove (← mkAppM ``Changes.Misses #[inner, low, high]) `(tactic| rivet_changes) with
    | .ok away =>
      return ← mkEqTrans (mkApp6 (mkConst ``MachineState.Except.sameMemory) memory.appArg! earlier inner kept address away)
        (← memoryKept names c address (mkApp (mkConst ``MachineState.memory) earlier))
    | .error error => failure := failure <|> some error.toMessageData
  throwError "rivet_changes: the nested block ending in{indentExpr memory.appArg!}\nmay change memory that \
    this block's change does not cover.\n{failure.getD m!""}"

-- What the facts say `memory` is, and what they say that is, each with a proof `s.memory = …`.
private meta partial def namesOf (memory same : Expr) : MetaM (Array (Expr × Expr)) := do
  let some (next, fact) ← factAbout memory | return #[(memory, same)]
  return #[(memory, same)] ++ (← namesOf next (← mkEqTrans same fact))

private meta def except (t s c : Expr) : TacticM Expr := do
  if t == s then return ← mkAppOptM ``MachineState.Except.refl #[s, c]
  let changed ← changedRegisters c
  let ranges ← changedRanges c
  let statement ← inferType (← mkAppOptM ``MachineState.Except.mk #[t, s, c])
  let .forallE _ registersType (.forallE _ memoryType _ _) _ := statement
    | throwError "rivet_changes: unexpected statement{indentExpr statement}"
  let registersGoal ← mkFreshExprSyntheticOpaqueMVar registersType
  let (register, goal) ← registersGoal.mvarId!.intro `register
  let (_, goal) ← goal.intro `out
  for case in ← goal.cases register do
    case.mvarId.withContext do
      let some decl := (← getLCtx).findFromUserName? `out | unreachable!
      let some name := case.ctorName | unreachable!
      if changed.contains name then
        let some inside := (← instantiateMVars decl.type).not? | unreachable!
        case.mvarId.assign (← mkAbsurd (← case.mvarId.getType) (← mkDecideProof inside) decl.toExpr)
      else
        case.mvarId.assign (← registerKept t s c (mkConst name))
  let memoryGoal ← mkFreshExprSyntheticOpaqueMVar memoryType
  let (address, goal) ← memoryGoal.mvarId!.intro `address
  let (away, goal) ← goal.intro `away
  let mut goal := goal
  for (pair, low, high) in ranges do
    let fact ← goal.withContext do
      let value ← mkAppM ``BitVec.toNat #[.fvar address]
      let type := mkOr (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[value, mkNatLit 1], low])
        (← mkAppM ``LE.le #[high, value])
      let proof := mkApp2 (.fvar away) pair (← member pair (ranges.map (·.1)))
      pure (type, proof)
    goal := (← (← goal.assert `away fact.1 fact.2).intro1P).2
  let start := mkApp (mkConst ``MachineState.memory) s
  let names ← namesOf start (← mkEqRefl start)
  goal.withContext do
    goal.assign (← memoryKept names c (.fvar address) (mkApp (mkConst ``MachineState.memory) t))
  mkAppOptM ``MachineState.Except.mk #[t, s, c, ← instantiateMVars registersGoal, ← instantiateMVars memoryGoal]

-- As a `simp` discharger it runs at reducible transparency, where a change does not unfold, and
-- `simp` checks the proof against the goal as stated.
@[tactic rivetChanges] meta def evalRivetChanges : Tactic := fun _ => withMainContext <| withTransparency .default do
  let goal ← getMainGoal
  let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let proof ← match_expr type with
    | MachineState.Except t s c => except t s c
    | Changes.Misses c low high => misses c low high type
    | Not inside =>
      let_expr Membership.mem _ _ _ coll register := inside
        | throwError "rivet_changes: not a goal about a change:{indentExpr type}"
      outside coll register
    | _ => throwError "rivet_changes: not a goal about a change:{indentExpr type}"
  goal.assign (← mkExpectedTypeHint proof (← goal.getType))

end ChangesTactic

open ChangesTactic in
-- A register that the block's start state has kept is read from the state it was kept from, so
-- facts about that state apply.
simproc [rivet] unchangedRegister (MachineState.registers _ _) := fun e => do
  let_expr MachineState.registers state register := e | return .continue
  let some name := register.constName? | return .continue
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr MachineState.Except t s c := ← instantiateMVars decl.type | continue
    unless t == state do continue
    let some changed ← try some <$> changedRegisters c catch _ => pure none | continue
    if changed.contains name then continue
    let out ← mkDecideProof
      (mkNot (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.registers) c, register]))
    return .visit { expr := mkApp2 (mkConst ``MachineState.registers) s register,
                    proof? := mkApp6 (mkConst ``MachineState.Except.sameRegisters) t s c decl.toExpr register out }
  return .continue

end Rivet
