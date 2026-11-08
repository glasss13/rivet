module
public import Rivet.Instructions
public meta import Lean
@[expose] public section
namespace Rivet

/-- Little-endian bytes of a 64-bit value, as stored by `MachineState.writeMemory`.
A named form, so that rewriting the value does not pass through `Fin.mk`'s proof. -/
def littleEndianBytes (value : BitVec 64) : Nat → Fin 256 :=
  fun offset => ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩

theorem MachineState.writeMemory_eq_storeBytes (state : MachineState) (address : Nat)
    (width : Width) (value : BitVec 64) :
    state.writeMemory address width value =
      { state with memory := state.memory.storeBytes address width.bytes (littleEndianBytes value) } :=
  rfl

end Rivet
end

-- The tactic implementation is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace Step

/-- The program and current state of an `Ensures P (· = s) Q` goal. -/
private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Ensures 3 do
    throwError "rivet_step: goal is not `Ensures P (· = s) Q`"
  let .lam _ _ body _ := type.getAppArgs[1]!
    | throwError "rivet_step: precondition is not `(· = s)`"
  let state := body.getAppArgs[2]!
  unless state.isFVar do throwError "rivet_step: the current state must be a variable"
  return (type.getAppArgs[0]!, state)

/-- The numeral `pc` from a hypothesis `state.status = .running pc`. -/
private meta def findPc (state : Expr) : MetaM Nat := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? | continue
    unless lhs.isAppOfArity ``MachineState.status 1 && lhs.appArg! == state do continue
    unless rhs.isAppOfArity ``ExecutionStatus.running 1 do continue
    if let some pc ← (evalNat rhs.appArg!).run then return pc
  throwError "rivet_step: no hypothesis `{state}.status = .running <numeral>`"

/-- The decoded operation at `pc`, and the fall-through address. -/
private meta def fetch (program : Expr) (pc : Nat) : MetaM (Expr × Nat) := withTransparency .all do
  let found ← whnf (← mkAppM ``Program.fetch #[program, mkNatLit pc])
  unless found.isAppOfArity ``Option.some 2 do
    throwError "rivet_step: no instruction at address {pc}"
  let instruction ← whnf found.appArg!
  unless instruction.isAppOfArity ``Instruction.mk 3 do
    throwError "rivet_step: cannot decode the instruction at {pc}"
  let operation ← whnf instruction.appArg!
  let next ← whnf (← mkAppM ``Program.nextAddress #[program, mkNatLit pc])
  let some next ← (evalNat next).run
    | throwError "rivet_step: cannot compute the address after {pc}"
  return (operation, next)

/-- The instruction contract for an operation, and the operands it takes
between `program address` and `initial`. -/
private meta def contractFor (operation : Expr) : MetaM (Name × Array Expr) := do
  let args := operation.getAppArgs
  let some ctor := operation.getAppFn.constName?
    | throwError "rivet_step: unrecognized operation {operation}"
  let name ← match ctor with
    | ``Op.nop => pure ``Rivet.nop | ``Op.movd => pure ``Rivet.movd
    | ``Op.pshufd => pure ``Rivet.pshufd | ``Op.loadXmm => pure ``Rivet.load_xmm
    | ``Op.storeXmm => pure ``Rivet.store_xmm | ``Op.lea => pure ``Rivet.lea
    | ``Op.movzx => pure ``Rivet.movzx | ``Op.movsxd => pure ``Rivet.movsxd
    | ``Op.mov => pure ``Rivet.move | ``Op.shift => pure ``Rivet.shift
    | ``Op.imul => pure ``Rivet.imul | ``Op.not => pure ``Rivet.bitwise_not
    | ``Op.inc => pure ``Rivet.inc | ``Op.dec => pure ``Rivet.dec
    | ``Op.jmp => pure ``Rivet.jump | ``Op.jcc => pure ``Rivet.branch
    | ``Op.setcc => pure ``Rivet.setcc | ``Op.cmovcc => pure ``Rivet.cmovcc
    | ``Op.push => pure ``Rivet.push | ``Op.pop => pure ``Rivet.pop
    | ``Op.call => pure ``Rivet.call | ``Op.ret => pure ``Rivet.return_
    | ``Op.binary =>
      match (← whnf args[0]!).constName? with
      | some ``BinaryOp.add => pure ``Rivet.add | some ``BinaryOp.sub => pure ``Rivet.sub
      | some ``BinaryOp.sbb => pure ``Rivet.sbb | some ``BinaryOp.cmp => pure ``Rivet.compare
      | some ``BinaryOp.test => pure ``Rivet.test | some ``BinaryOp.and => pure ``Rivet.bitwise_and
      | some ``BinaryOp.or => pure ``Rivet.bitwise_or | _ => pure ``Rivet.bitwise_xor
    | _ => throwError "rivet_step: unsupported operation {operation}"
  return (name, if ctor == ``Op.binary then args.extract 1 3 else args)

/-- Apply a contract to its explicit arguments. Optional parameters take their
defaults. Every side condition (an auto-parameter, or a remaining explicit
hypothesis such as RET's `slot`) becomes a goal named after its parameter. -/
private meta def instantiate (name : Name) (explicit : Array Expr) : MetaM (Expr × Array MVarId) := do
  let mut proof ← mkConstWithFreshMVarLevels name
  let mut type ← inferType proof
  let mut remaining := explicit.toList
  let mut sides : Array MVarId := #[]
  repeat
    let .forallE binder domain body info := type | break
    let mut argument := domain
    if let some default := domain.getOptParamDefault? then
      argument := default
    else if domain.isAutoParam then
      let goal ← mkFreshExprMVar domain.consumeTypeAnnotations .syntheticOpaque binder
      sides := sides.push goal.mvarId!
      argument := goal
    else if info.isExplicit then
      match remaining with
      | next :: rest =>
        remaining := rest
        argument := next
      | [] =>
        let goal ← mkFreshExprMVar domain .syntheticOpaque binder
        sides := sides.push goal.mvarId!
        argument := goal
    else
      argument ← mkFreshExprMVar domain
    proof := mkApp proof argument
    type := body.instantiate1 argument
  return (proof, sides)

/-- Try to prove one side condition. Cheap checks (`assumption`, `rfl`, `decide`)
always run first; then the caller's discharger if given, otherwise `simp [*]`,
which rewrites only the side condition with the current facts. -/
private meta def discharge (tactic? : Option Syntax) (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  setGoals [goal]
  try
    let fallback ← match tactic? with
      | some tactic => pure (⟨tactic⟩ : TSyntax `tactic)
      | none => `(tactic| (simp [*, MachineState.canRead, MachineState.canWrite,
          Address.evaluate, Scale.value]; done))
    evalTactic (← `(tactic| first | assumption | rfl | decide +kernel | ($fallback; done)))
    if (← getGoals).isEmpty then return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- Every `MachineState` field, in declaration order. -/
private meta def fields : List Name :=
  [`registers, `xmmRegisters, `signFlag, `zeroFlag, `carryFlag, `memory, `status, `readHistory]

/-- Facts `state.field = …` about a state. -/
private meta def factsAbout (state : FVarId) : MetaM (Array LocalDecl) := do
  let mut facts := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | continue
    if lhs.isApp && lhs.getAppNumArgs == 1 && lhs.appArg! == .fvar state &&
        (lhs.getAppFn.constName?.map (·.getPrefix == ``MachineState)).getD false then
      facts := facts.push decl
  return facts

/-- Substitute a temporary state's facts into every hypothesis that mentions it,
then clear it. A new fact that still mentions it through an untracked field is
dropped. If anything else still mentions it, the state is kept, with a warning. -/
private meta def retire (old : FVarId) : TacticM Unit := withMainContext do
  let oldFacts ← factsAbout old
  let oldIds := oldFacts.map (·.fvarId)
  let mut targets : Array Ident := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.fvarId == old || oldIds.contains decl.fvarId then continue
    if decl.userName.hasMacroScopes then continue
    if (← instantiateMVars decl.type).containsFVar old then targets := targets.push (mkIdent decl.userName)
  if !targets.isEmpty then
    let lemmas ← oldFacts.mapM fun decl => do
      let term ← Term.exprToSyntax (.fvar decl.fvarId)
      `(Lean.Parser.Tactic.simpLemma| $term:term)
    let locations : Array (TSyntax `term) := targets.map (⟨·.raw⟩)
    evalTactic (← `(tactic| try simp +contextual only [$lemmas,*, Condition.holds, reduceCtorEq,
        ↓reduceIte, eq_self_iff_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq,
        List.append_assoc, List.cons_append, List.nil_append] at $locations*))
  let known ← oldFacts.filterMapM fun decl => do
    let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | return none
    return lhs.getAppFn.constName?
  let mut goal ← getMainGoal
  let mut keepOld := false
  for decl in ← goal.withContext getLCtx do
    if decl.isImplementationDetail || decl.fvarId == old || oldIds.contains decl.fvarId then continue
    let type ← instantiateMVars decl.type
    unless type.containsFVar old do continue
    let untracked := (type.find? fun e => e.isApp && e.appArg! == .fvar old &&
      match e.getAppFn.constName? with
      | some n => n.getPrefix == ``MachineState && !known.contains n
      | none => false).isSome
    if untracked && decl.userName.toString.startsWith "rivet_fact_" then
      goal ← goal.tryClear decl.fvarId
    else keepOld := true
  goal ← goal.tryClearMany oldIds
  if keepOld then
    logWarning m!"rivet_step: kept the previous state, because some facts still refer to it"
  else goal ← goal.tryClear old
  replaceMainGoal [goal]

private meta def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

end Step

/--
`rivet_step` executes the instruction at the current address of an
`Ensures program (· = s) Q` goal, using that instruction's contract.

It needs a hypothesis `s.status = .running pc` for a numeral `pc`, and continues
with a fresh successor state plus one fact per field: `t.registers = …`,
`t.memory = …`, `t.status = .running next`, and so on.

* **States.** An unnamed successor is inaccessible (`s✝`) and temporary: on the
  next step its facts are substituted into the new facts and it is cleared, so
  facts stay expressed in terms of the states you named. `rivet_step as t` names
  the successor and keeps it as a checkpoint.
* **Facts** are inaccessible (`h✝`). Use them with `simp [*]`, `simp_all`,
  `omega` or `assumption`, or retrieve one by statement, e.g. `‹t.memory = _›`.
* **Side conditions** the discharger cannot prove remain as goals tagged with
  the contract's parameter name (`case writable`, `case slot`, …).
  `rivet_step (disch := tac)` replaces the fallback discharger (`simp [*]`);
  `assumption`, `rfl` and `decide` are always tried first.
* **Conditional jumps** produce goals tagged `taken` and `fallthrough`, each with
  its path condition as a hypothesis.
* `rivet_step tracking [status, registers, memory]` records only those fields
  (default: all). Later facts that depend on an untracked field are dropped.
* `rivet_step using e` applies the contract application `e` instead of looking
  one up.
-/
syntax (name := rivetStep) "rivet_step" (" (" &"disch" " := " tacticSeq ")")? (" using " term)?
  (" as " ident)? (" tracking " "[" ident,* "]")? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (program, old) ← goalParts (← getMainGoal)
  let pc ← findPc old
  let (operation, next) ← fetch program pc
  -- Inaccessible (generated) states are temporary; states you named are kept.
  let temporary := (← old.fvarId!.getUserName).hasMacroScopes
  let discharger : Option Syntax := if stx[1].getNumArgs > 0 then some stx[1][3] else none
  let named? : Option Name := if stx[3].getNumArgs > 0 then some stx[3][1].getId else none
  let tracked : List Name :=
    if stx[4].getNumArgs > 0 then (stx[4][2].getSepArgs.map (·.getId)).toList else fields
  for field in tracked do
    unless fields.contains field do throwError "rivet_step: unknown field `{field}`"
  -- 1. The contract, with side conditions as goals; discharge what we can.
  let mut unsolved : Array MVarId := #[]
  let contract : Term ← if stx[2].getNumArgs > 0 then pure ⟨stx[2][1]⟩ else do
    let (name, operands) ← contractFor operation
    let (proof, sides) ← instantiate name (#[program, mkNatLit pc] ++ operands ++ #[old])
    let main ← getMainGoal
    for side in sides do
      unless ← discharge discharger side do unsolved := unsolved.push side
    setGoals [main]
    Term.exprToSyntax proof
  -- 2. Continue from a fresh successor. Internal names are fixed and replaced at the end.
  let successor := mkIdent `rivet_next
  let equation := mkIdent `rivet_step_equation
  evalTactic (← `(tactic| refine Rivet.Ensures.bind $contract fun $successor $equation => ?_))
  let mut main? : Option MVarId := none
  for goal in ← getGoals do
    if main?.isNone && (← goal.withContext do
        return ((← getLCtx).findFromUserName? equation.getId).isSome) then
      main? := some goal
    else unsolved := unsolved.push goal
  let some main := main? | throwError "rivet_step: continuation goal not found"
  setGoals [main]
  -- Unpack existential results (IMUL's unconstrained flags) down to the equation.
  repeat
    let isExists ← withMainContext do
      let some decl := (← getLCtx).findFromUserName? equation.getId | return false
      return (← whnfR (← instantiateMVars decl.type)).isAppOfArity ``Exists 2
    unless isExists do break
    evalTactic (← `(tactic| obtain ⟨_, $equation⟩ := $equation))
  -- 3. One fact per tracked field, normalized.
  let mut internal : Array Name := #[]
  for field in fields do
    unless tracked.contains field do continue
    let fact := Name.mkSimple s!"rivet_fact_{field}"
    evalTactic (← `(tactic| have $(mkIdent fact) := congrArg $(mkIdent (`Rivet.MachineState ++ field)) $equation))
    internal := internal.push fact
  evalTactic (← `(tactic| clear $equation))
  let programStx ← Term.exprToSyntax program
  let nextFact ← `(show Program.nextAddress $programStx $(quote pc) = $(quote next) by decide +kernel)
  let locations : Array (TSyntax `term) := internal.map (⟨mkIdent ·⟩)
  evalTactic (← `(tactic| try simp only [$nextFact:term, MachineState.writeOperand,
      MachineState.readOperand, MachineState.recordRead, MachineState.write,
      MachineState.writeMemory_eq_storeBytes, Operand.width, Width.bits, Width.bytes,
      BitVec.setWidth_eq, List.append_assoc, List.cons_append, List.nil_append] at $locations*))
  -- 4. Conditional jump: two tagged goals, each with its path condition.
  let isBranch := operation.isAppOfArity ``Op.jcc 2 && tracked.contains `status
  if isBranch then
    let condition ← Term.exprToSyntax operation.getAppArgs[0]!
    let oldStx ← Term.exprToSyntax old
    let status := mkIdent `rivet_fact_status
    let path := mkIdent `rivet_fact_path
    evalTactic (← `(tactic| by_cases $path : Condition.holds $condition $oldStx = true <;>
      simp only [$path:ident, ↓reduceIte, Bool.false_eq_true] at $status:ident))
    -- State the path condition with flags rather than `Condition.holds`.
    evalTactic (← `(tactic| all_goals try simp only [Condition.holds, Bool.not_eq_true',
      Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false]
      at $path:ident))
    internal := internal.push `rivet_fact_path
  -- 5. In each goal: retire a temporary predecessor, then give the new state and
  --    its facts their final names (yours, or inaccessible).
  let finalName ← match named? with
    | some name => pure name
    | none => mkFreshUserName `s
  let mut finished := #[]
  for (branch, index) in (← getGoals).zipIdx do
    setGoals [branch]
    if temporary then retire old.fvarId!
    let mut goal ← getMainGoal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        goal ← goal.rename decl.fvarId (← mkFreshUserName `h)
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    finished := finished.push goal
  setGoals (finished.toList ++ unsolved.toList)

end Rivet
end
