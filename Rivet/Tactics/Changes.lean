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

private meta def within (smaller larger type : Expr) : TacticM Expr := do
  let allowed ← changedRegisters larger
  for register in ← changedRegisters smaller do
    unless allowed.contains register do
      throwError "rivet_changes: register `{mkConst register}` is in the change{indentExpr smaller}\nand not in \
        the change it must lie within:{indentExpr larger}"
  let_expr And registers memory := ← unfolded type
    | throwError "rivet_changes: unexpected statement{indentExpr type}"
  let covers ← changedRanges larger
  let ranges ← changedRanges smaller
  let memoryProof ← forEachItem memory (ranges.map (·.1)) fun pair covered => do
    let some (_, low, high) := ranges.find? (·.1 == pair) | unreachable!
    for (cover, coverLow, coverHigh) in covers do
      let inside := mkAnd (← mkAppM ``LE.le #[coverLow, low]) (← mkAppM ``LE.le #[high, coverHigh])
      if let .ok proof ← prove inside `(tactic| rivet_arith) then
        return ← mkAppOptM ``Exists.intro
          #[none, covered.appArg!, cover, ← mkAppM ``And.intro #[← member cover (covers.map (·.1)), proof]]
    throwError "rivet_changes: the changed range {showRange low high} is not shown to lie inside a range \
      of the change it must lie within:{indentExpr larger}"
  mkAppM ``And.intro #[← mkDecideProof registers, memoryProof]

-- The most recent fact `lhs = …` in scope.
private meta def factAbout (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut found := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, left, right) := (← instantiateMVars decl.type).eq? | continue
    if left == lhs then found := some (right, decl.toExpr)
  return found

-- The value of a register in a state, followed through the steps' facts to the state they
-- start from: the value, whether a step wrote it, and a proof that the register holds it.
private meta partial def readRegister (state register : Expr) : MetaM (Expr × Bool × Expr) := do
  let read := mkApp2 (mkConst ``MachineState.registers) state register
  let some (function, fact) ← factAbout (mkApp (mkConst ``MachineState.registers) state)
    | return (read, false, ← mkEqRefl read)
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

private meta def registerKept (t s c register : Expr) : TacticM Expr := do
  let goal ← mkEq (mkApp2 (mkConst ``MachineState.registers) t register)
    (mkApp2 (mkConst ``MachineState.registers) s register)
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← instantiateMVars decl.type) == goal then return decl.toExpr
  let (value, written, proof) ← readRegister t register
  let mut proof := proof
  if written then
    let mut definitions := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let some (_, .fvar memory, _) := (← instantiateMVars decl.type).eq? | continue
      if (← memory.getType).isConstOf ``Memory then
        definitions := definitions.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax decl.toExpr):term))
    let restored ← mkEq value (mkApp2 (mkConst ``MachineState.registers) s register)
    match ← prove restored `(tactic| first
        | rfl
        | simp (disch := rivet_arith) [$definitions,*, rivet, Memory.readBytes_storeBytes_inside,
            Memory.readBytes_storeBytes_outside]) with
    | .ok same => proof ← mkEqTrans proof same
    | .error _ =>
      let unnamed := if (← t.fvarId!.getUserName).hasMacroScopes then
        m!"\nName the last state (`rivet_step … as t`): its registers are then stated over the block's start." else m!""
      throwError "rivet_changes: register `{register}` is written, and it is not in the change\
        {indentExpr c}\nIf it is restored, prove this first, and it will be used:{indentExpr goal}\n\
        Its value is{indentExpr value}{unnamed}"
  unless ← isDefEq (← inferType proof) goal do
    throwError "rivet_changes: could not follow register `{register}` from{indentExpr t}\nback to\
      {indentExpr s}\nThe steps' facts give{indentExpr value}"
  return proof

private meta partial def memoryKept (s c address memory : Expr) : TacticM Expr := do
  let read := mkApp memory address
  if let some state := memory.app1? ``MachineState.memory then
    if state == s then return ← mkEqRefl read
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
      (← memoryKept s c address earlier)
  let some (earlier, fact) ← factAbout memory
    | throwError "rivet_changes: nothing in scope says what this memory is, relative to{indentExpr s}\n\
        {indentExpr memory}"
  return ← mkEqTrans (← mkCongrFun fact address) (← memoryKept s c address earlier)

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
  goal.withContext do
    goal.assign (← memoryKept s c (.fvar address) (mkApp (mkConst ``MachineState.memory) t))
  mkAppOptM ``MachineState.Except.mk #[t, s, c, ← instantiateMVars registersGoal, ← instantiateMVars memoryGoal]

@[tactic rivetChanges] meta def evalRivetChanges : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let proof ← match_expr type with
    | MachineState.Except t s c => except t s c
    | Changes.Misses c low high => misses c low high type
    | Changes.Within smaller larger => within smaller larger type
    | Not inside =>
      let_expr Membership.mem _ _ _ coll register := inside
        | throwError "rivet_changes: not a goal about a change:{indentExpr type}"
      outside coll register
    | _ => throwError "rivet_changes: not a goal about a change:{indentExpr type}"
  goal.assign proof

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
