module
public import Rivet.Laws.Changes
public import Rivet.Laws.SimpSet
public meta import Lean
-- What the read-back finds in scope: the steps' facts, the stores', the nested blocks' `Except`, and
-- the states and hypotheses they make; and the read-back of registers.
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

namespace Step

-- Marks a store's memory `mₙ`, with the instruction that made it, for errors that name the store.
inductive StoredBy (memory : Memory) (address : Nat) (operation : Op) : Prop
  | intro

end Step

namespace ReadBack

meta partial def listItems (list : Expr) : MetaM (Array Expr) := do
  let list ← whnfD list
  if list.isAppOfArity ``List.nil 1 then return #[]
  if list.isAppOfArity ``List.cons 3 then return #[list.getArg! 1] ++ (← listItems (list.getArg! 2))
  throwError "a change lists its registers and regions one by one; this is not such a list:{indentExpr list}"

-- A read of a register or a vector register: where a change lists such registers, and the law that a
-- block keeps the ones its change does not list.
meta def registerFile? (read : Expr) : Option (Name × Name) :=
  if read.isAppOfArity ``MachineState.registers 2 then
    some (``Changes.registers, ``MachineState.Except.sameRegisters)
  else if read.isAppOfArity ``MachineState.xmmRegisters 2 then some (``Changes.xmm, ``MachineState.Except.sameXmm)
  else none

meta def changedRegisters (c : Expr) (listed : Name := ``Changes.registers) : MetaM (Array Name) := do
  (← listItems (mkApp (mkConst listed) c)).mapM fun register => do
    let some name := (← whnfD register).constName?
      | throwError "a change names its registers; this is not a register name:{indentExpr register}"
    return name

-- What the block did, read from the context once: what each step says of the state it ends in, and what
-- a call's postcondition says of the state it ends in (one register, `t.registers .rsp = …`, only a call
-- says); each store's memory and what it is; and each nested block's `t.Except earlier c`, newest first.
meta structure History where
  instructions : Std.HashMap Expr (Expr × Expr) := {}
  equations : Std.HashMap Expr (Expr × Expr) := {}
  stores : Std.HashMap FVarId (Expr × Expr) := {}
  nested : Std.HashMap Expr (Array (Expr × Expr × Expr)) := {}
  later : Std.HashSet FVarId := {}
  users : Array LocalDecl := #[]
  lets : Array FVarId := #[]

meta def isStepState (state : Expr) : MetaM Bool := do
  let .fvar id := state | return false
  return (annotation? `Rivet.Step.state (← id.getType)).isSome

meta def History.read : MetaM History := do
  let mut h : History := {}
  for decl in ← getLCtx do
    if (annotation? `Rivet.Step.state decl.type).isSome then
      h := { h with later := h.later.insert decl.fvarId }
      continue
    if decl.isImplementationDetail then
      if let some (memory, pc, op) := decl.type.app3? ``Step.StoredBy then
        h := { h with instructions := h.instructions.insert memory (pc, op) }
      continue
    let type ← instantiateMVars decl.type
    if let some (t, earlier, c) := type.app3? ``MachineState.Except then
      if t == earlier then continue
      h := { h with nested := h.nested.insert t (#[(earlier, c, decl.toExpr)] ++ h.nested[t]?.getD #[]) }
      if t.isFVar then h := { h with later := h.later.insert t.fvarId! }
      continue
    if let some (_, lhs, rhs) := type.eq? then
      if let .app (.const field _) state := lhs then
        if field.getPrefix == ``MachineState && (← isStepState state) then
          h := { h with equations := h.equations.insertIfNew lhs (rhs, decl.toExpr) }
          continue
      if let .fvar id := lhs then
        if rhs.isAppOfArity ``Memory.storeBytes 4 then
          h := { h with stores := h.stores.insertIfNew lhs.fvarId! (rhs, decl.toExpr), later := h.later.insert id }
          continue
    if decl.isLet then h := { h with lets := h.lets.push decl.fvarId }
    if ← isProp type then h := { h with users := h.users.push decl }
  return h

meta def History.keptBy (h : History) (state : Expr) := h.nested[state]?.getD #[]

-- A record is opened only as you could open it: by the fields you can name, `h.field`, and as a goal by a
-- constructor you can name. A field or constructor made private has a private name, not the record's
-- name and its own.
meta def nameable (record part : Name) : Bool :=
  part == .str record part.getString!

meta def splits (type : Expr) : CoreM Bool := do
  let some name := type.getAppFn.constName? | return false
  let env ← getEnv
  return isStructure env name && nameable name (getStructureCtor env name).name

-- What a fact says, part by part: an `abbrev`'s body, and a record's fields; the records named in `whole` kept whole.
meta partial def parts (proof type : Expr) (whole : Array Name := #[]) : MetaM (Array (Expr × Expr)) := do
  let type ← whnfR (← instantiateMVars type)
  unless ← isProp type do return #[]
  let some name := type.getAppFn.constName? | return #[(proof, type)]
  let env ← getEnv
  unless isStructure env name && !whole.contains name do return #[(proof, type)]
  let fields := (getStructureFields env name).filter fun field =>
    (getProjFnForField? env name field).any (nameable name)
  if fields.isEmpty then return #[(proof, type)]
  fields.flatMapM fun field => do
    let part ← mkProjection proof field
    parts part (← inferType part) whole

-- An `abbrev` applied to a state or to what a later state holds, unfolded where it is read back, so that
-- what it reads is read back too and your facts reach inside it.
meta def openAbbrev (later : Std.HashSet FVarId) : Simp.DSimproc := fun e => do
  let some name := e.getAppFn.constName? | return .continue
  if (← isProjectionFn name) || !(← isReducible name) then return .continue
  let toState ← e.getAppArgs.anyM fun argument => do
    if argument.hasAnyFVar later.contains then return true
    return argument.isFVar && (← inferType argument).isConstOf ``MachineState
  unless toState do return .continue
  let some unfolded ← unfoldDefinition? e | return .continue
  return .visit unfolded.headBeta

-- The nested block that ended in the state of a register read and leaves the register alone: its
-- start, change and `Except`.
meta def History.leaves (history : History) (read : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (listed, _) := registerFile? read | return none
  let some name := read.appArg!.constName? | return none
  (history.keptBy read.appFn!.appArg!).findM? fun (_, c, _) => do
    let some changed ← try some <$> changedRegisters c listed catch _ => pure none | return false
    return !changed.contains name

-- A register a nested block's change does not list, read back across it.
meta def unchangedRegister (history : History) : Simp.Simproc := fun e => do
  let some (listed, law) := registerFile? e | return .continue
  let some (earlier, c, kept) ← history.leaves e | return .continue
  let state := e.appFn!.appArg!
  let register := e.appArg!
  let out ← mkDecideProof (mkNot (← mkAppM ``Membership.mem #[mkApp (mkConst listed) c, register]))
  return .visit { expr := mkApp2 e.appFn!.appFn! earlier register,
                  proof? := mkApp6 (mkConst law) state earlier c kept register out }

end ReadBack

end Rivet.Internal
