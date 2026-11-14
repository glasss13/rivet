module
public import Rivet.Laws.Changes
public import Rivet.Laws.SimpSet
public meta import Lean
-- Reading registers back: through the steps' facts, and through each nested block that left the
-- register alone.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace ReadBack

meta partial def listItems (list : Expr) : MetaM (Array Expr) := do
  let list ← whnfD list
  if list.isAppOfArity ``List.nil 1 then return #[]
  if list.isAppOfArity ``List.cons 3 then return #[list.getArg! 1] ++ (← listItems (list.getArg! 2))
  throwError "a change lists its registers and ranges one by one; this is not such a list:{indentExpr list}"

meta def changedRegisters (c : Expr) : MetaM (Array Name) := do
  (← listItems (mkApp (mkConst ``Changes.registers) c)).mapM fun register => do
    let some name := (← whnfD register).constName?
      | throwError "a change names its registers; this is not a register name:{indentExpr register}"
    return name

meta def changedRanges (c : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  (← listItems (mkApp (mkConst ``Changes.memory) c)).mapM fun range => do
    let pair ← whnfD range
    unless pair.isAppOfArity ``Prod.mk 4 do
      throwError "a change gives each range as `(low, high)`; this is not one:{indentExpr range}"
    return (range, pair.getArg! 2, pair.getArg! 3)

-- What each step says of the state it ends in.
meta def stepFacts : MetaM (Array Expr) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | continue
    if lhs.getAppNumArgs == 1 && lhs.appArg!.isFVar &&
        (lhs.getAppFn.constName?.map (·.getPrefix == ``MachineState)).getD false then found := found.push decl.toExpr
  return found

-- A store's memory, and what it is.
meta def storeFacts : MetaM (Array (FVarId × Expr × Expr)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, .fvar memory, stored) := (← instantiateMVars decl.type).eq? | continue
    if (← memory.getType).isConstOf ``Memory then found := found.push (memory, stored, decl.toExpr)
  return found

-- Every `state.Except earlier c` in scope, newest first: the nested blocks that ended in `state`.
meta def keptBy (state : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr MachineState.Except t earlier c := ← instantiateMVars decl.type | continue
    if t == state then found := found.push (earlier, c, decl.toExpr)
  return found.reverse

-- The states a step or a nested block ended in, and the memories the stores made: what is read back.
meta def later : MetaM (Array FVarId) := do
  let mut found := (← storeFacts).map (·.1)
  for fact in ← stepFacts do
    let some (_, lhs, _) := (← instantiateMVars (← inferType fact)).eq? | continue
    -- Its status alone does not make a state a later one: the block's start has one too.
    if lhs.isAppOf ``MachineState.status then continue
    unless found.contains lhs.appArg!.fvarId! do found := found.push lhs.appArg!.fvarId!
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr MachineState.Except t _ _ := ← instantiateMVars decl.type | continue
    if t.isFVar && !found.contains t.fvarId! then found := found.push t.fvarId!
  return found

-- The hypotheses a goal's parts may follow from: not the steps' facts, the stores' or the nested
-- blocks' `Except`, which the read-back uses itself.
meta def hypotheses : MetaM (Array LocalDecl) := do
  let own := (← stepFacts) ++ (← storeFacts).map (·.2.2)
  (← getLCtx).foldlM (init := #[]) fun found decl => do
    if decl.isImplementationDetail || own.contains decl.toExpr then return found
    let type ← instantiateMVars decl.type
    if !(← isProp type) || type.isAppOf ``MachineState.Except || type.isAppOf `Rivet.Block then return found
    return found.push decl

-- What a fact says, part by part: an `abbrev`'s body, and a record's fields.
meta partial def parts (proof type : Expr) : MetaM (Array (Expr × Expr)) := do
  let type ← whnfR (← instantiateMVars type)
  let some name := type.getAppFn.constName? | return #[(proof, type)]
  unless isStructure (← getEnv) name do return #[(proof, type)]
  (getStructureFields (← getEnv) name).flatMapM fun field => do
    let part ← mkProjection proof field
    parts part (← inferType part)

-- The `abbrev`s `e` applies to a later state, unfolded where it is read back so that what they read
-- is read back too.
meta def opened (e : Expr) : MetaM (Array Name) := do
  let later ← later
  let found ← IO.mkRef (#[] : Array Name)
  forEachExpr (← instantiateMVars e) fun e => do
    let some name := e.getAppFn.constName? | return
    if (← found.get).contains name || (← isProjectionFn name) || !(← isReducible name) then return
    if e.getAppArgs.any fun argument => later.any (argument.containsFVar ·) then found.modify (·.push name)
  found.get

meta def lemmas (names : Array Name) (facts : Array Expr) (fixed : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TermElabM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let names ← names.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
  let facts ← facts.mapM fun fact => do `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax fact):term)
  return fixed ++ names ++ facts

-- Reads the registers and addresses of `target`, or of hypotheses, back. No arithmetic.
meta def registersBack (target : Expr) (locations : Array Term := #[]) : TermElabM (TSyntax `tactic) := do
  let all ← lemmas (← opened target) (← stepFacts) #[
    ← `(Lean.Parser.Tactic.simpLemma| rivet), ← `(Lean.Parser.Tactic.simpLemma| reduceCtorEq),
    ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte), ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceSub),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceAdd), ← `(Lean.Parser.Tactic.simpLemma| BitVec.reduceOfNat),
    ← `(Lean.Parser.Tactic.simpLemma| BitVec.sub_zero), ← `(Lean.Parser.Tactic.simpLemma| BitVec.add_zero)]
  if locations.isEmpty then `(tactic| simp only [$all,*]) else `(tactic| simp only [$all,*] at $[$locations]* ⊢)

end ReadBack

open ReadBack in
simproc [rivet] unchangedRegister (MachineState.registers _ _) := fun e => do
  let_expr MachineState.registers state register := e | return .continue
  let some name := register.constName? | return .continue
  for (earlier, c, kept) in ← keptBy state do
    let some changed ← try some <$> changedRegisters c catch _ => pure none | continue
    if changed.contains name then continue
    let out ← mkDecideProof
      (mkNot (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.registers) c, register]))
    return .visit { expr := mkApp2 (mkConst ``MachineState.registers) earlier register,
                    proof? := mkApp6 (mkConst ``MachineState.Except.sameRegisters) state earlier c kept register out }
  return .continue

end Rivet
