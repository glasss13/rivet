module
public import Rivet.Laws.Instructions
public import Rivet.Tactics.Fetch
-- `rivet_step`: executes one instruction of an `Ensures` goal through its contract.
public meta import Lean

-- The tactic implementation is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace Step

/-- The image and current state of an `Ensures image (· = s) Q` goal. -/
private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Ensures 3 do
    throwError "rivet_step: goal is not `Ensures P (· = s) Q`"
  let .lam _ _ body _ := type.getAppArgs[1]!
    | throwError "rivet_step: precondition is not `(· = s)`"
  let state := body.getAppArgs[2]!
  unless state.isFVar do throwError "rivet_step: the current state must be a variable"
  return (type.getAppArgs[0]!, state)

/-- The address in the hypothesis `state.status = .running address`, its value, and
the hypothesis. The address is a literal or a definition that unfolds to one. -/
private meta def findPc (state : Expr) : MetaM (Expr × Nat × Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? | continue
    unless lhs.isAppOfArity ``MachineState.status 1 && lhs.appArg! == state do continue
    unless rhs.isAppOfArity ``ExecutionStatus.running 1 do continue
    -- A numeral, or a definition such as an imported `entry` that unfolds to one.
    let address := rhs.appArg!
    if let some pc ← Fetch.addressValue? address then return (address, pc, .fvar decl.fvarId)
  throwError "rivet_step: no hypothesis `{state}.status = .running <address>`"

/-- The instruction at `pc` (as `Instruction.mk address length operation`) and a proof
that `Program.fetch` returns it, from the shared lookup `Fetch.prove`: constant time
in the program size for generated programs. -/
private meta def fetch (program address : Expr) (pc : Nat) : MetaM (Expr × Expr) := do
  let some found ← Fetch.prove program address pc
    | throwError "rivet_step: no instruction at address {pc}"
  return found

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
hypothesis) becomes a goal named after its parameter. -/
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

/-- Every `MachineState` field, in declaration order. -/
private meta def fields : List Name :=
  [`registers, `xmmRegisters, `signFlag, `zeroFlag, `carryFlag, `memory, `status]

/-- Notes (the facts `t.field = …` a step records) are named under a hygiene module of
their own: they display as `h✝` like any inaccessible hypothesis, but a path condition or
a hypothesis of yours with the same shape (`t.carryFlag = true`) is never taken for one. -/
private meta def noteModule : Name := `Rivet.Step.note

/-- A fresh inaccessible name for a note. -/
private meta def noteName : CoreM Name := do
  return { extractMacroScopes (← mkFreshUserName `h) with ctx := noteModule }.review

private meta def isNote (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.hasMacroScopes &&
    (extractMacroScopes decl.userName).ctx == noteModule

/-- The state a note `state.field = …` is about. -/
private meta def noteState? (decl : LocalDecl) : MetaM (Option FVarId) := do
  unless isNote decl do return none
  let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | return none
  unless lhs.isApp && lhs.getAppNumArgs == 1 &&
      (lhs.getAppFn.constName?.map (·.getPrefix == ``MachineState)).getD false do return none
  let .fvar state := lhs.appArg! | return none
  return some state

/-- The notes about any of `states`. -/
private meta def notesAbout (states : Array FVarId) : MetaM (Array LocalDecl) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if let some state ← noteState? decl then
      if states.contains state then found := found.push decl
  return found

/-- The states `rivet_step` introduced: those with notes. The block's start has none. -/
private meta def introducedStates : MetaM (Array FVarId) := do
  let mut states := #[]
  for decl in ← getLCtx do
    if let some state ← noteState? decl then
      unless states.contains state do states := states.push state
  return states

/-- Rewrite the hypotheses `targets` with `facts`, in one `simp +contextual` pass that
follows chains of facts to their end; `+contextual` merges the nested `if`s of a rewritten
register file into one branch per written register. -/
private meta def rewriteAt (facts : Array LocalDecl) (targets : Array FVarId) : TacticM Unit :=
    withMainContext do
  if facts.isEmpty || targets.isEmpty then return
  let lemmas ← facts.mapM fun decl => do
    let term ← Term.exprToSyntax (.fvar decl.fvarId)
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let stx ← `(tactic| simp +contextual only [$lemmas,*, Condition.holds, reduceCtorEq,
      ↓reduceIte, eq_self_iff_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  try
    let (result?, _) ← simpGoal (← getMainGoal) ctx simprocs (simplifyTarget := false)
      (fvarIdsToSimp := targets)
    replaceMainGoal (match result? with | some (_, goal) => [goal] | none => [])
  catch _ => pure ()

/-- Clear `states` and their notes from `goal`. A state that the goal or a hypothesis
other than its notes still mentions stays, with its notes, and so do the states those
notes mention. -/
private meta def dropStates (goal : MVarId) (states : Array FVarId) : MetaM MVarId :=
    goal.withContext do
  if states.isEmpty then return goal
  let mut uses : Array Expr := #[← instantiateMVars (← goal.getType)]
  let mut notes : Array (FVarId × LocalDecl) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || states.contains decl.fvarId then continue
    match ← noteState? decl with
    | some state => if states.contains state then notes := notes.push (state, decl)
                    else uses := uses.push (← instantiateMVars decl.type)
    | none => uses := uses.push (← instantiateMVars decl.type)
  let mut kept : Array FVarId := #[]
  let mut grown := true
  while grown do
    grown := false
    for state in states do
      if kept.contains state || !uses.any (·.containsFVar state) then continue
      kept := kept.push state
      grown := true
      for (subject, decl) in notes do
        if subject == state then uses := uses.push (← instantiateMVars decl.type)
  let goal ← goal.tryClearMany ((notes.filter (!kept.contains ·.1)).map (·.2.fvarId))
  goal.tryClearMany (states.filter (!kept.contains ·))

/-- Name a checkpoint. The new state's facts (`rivet_fact_*`), the path conditions, and
your hypotheses are rewritten with the notes of every state introduced before it, named or
not, so that they are stated in terms of the block's start; then those states and their
notes are cleared. A new fact that still mentions one (through an untracked field) is
dropped; a state anything else still mentions stays, with its notes. -/
private meta def checkpoint : TacticM Unit := withMainContext do
  let states ← introducedStates
  if states.isEmpty then return
  let mentions (type : Expr) : Bool := states.any (type.containsFVar ·)
  let mut targets := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || isNote decl || states.contains decl.fvarId then continue
    if mentions (← instantiateMVars decl.type) then targets := targets.push decl.fvarId
  rewriteAt (← notesAbout states) targets
  let some goal := (← getGoals).head? | return
  let mut goal := goal
  for decl in ← goal.withContext getLCtx do
    if decl.isImplementationDetail || !decl.userName.toString.startsWith "rivet_fact_" then continue
    if mentions (← instantiateMVars decl.type) then goal ← goal.tryClear decl.fvarId
  replaceMainGoal [← dropStates goal states]

/-- Whether `tactic` closes `goal`; if not, nothing changes. -/
private meta def closes (tactic : TSyntax `tactic) (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic tactic
    if (← getGoals).isEmpty then return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- State a side condition over the block's start: rewrite it with the notes of every
state the tactic introduced, named or not, then clear those states and their notes from
this goal's context unless something still mentions them. The rewrite costs as many steps
as were taken since the last checkpoint, plus one. Returns `none` if the rewrite closes
the goal, and otherwise the goal and whether the rewrite applied. -/
private meta def overStart (goal : MVarId) : TacticM (Option (MVarId × Bool)) := goal.withContext do
  let states ← introducedStates
  if states.isEmpty then return some (goal, false)
  let mut goal := goal
  let rewritten := states.any ((← instantiateMVars (← goal.getType)).containsFVar ·)
  if rewritten then
    let lemmas ← (← notesAbout states).mapM fun decl => do
      let term ← Term.exprToSyntax (.fvar decl.fvarId)
      `(Lean.Parser.Tactic.simpLemma| $term:term)
    setGoals [goal]
    evalTactic (← `(tactic| try simp only [$lemmas,*, reduceCtorEq, ↓reduceIte, eq_self_iff_true]))
    let [next] ← getGoals | return none
    goal := next
  return some (← dropStates goal states, rewritten)

/-- Try to prove one side condition. It is first reduced by the `rivet` simp set,
which closes register and immediate accesses and states memory accesses as `permits`
over register reads. Cheap checks (`rfl` and `decide` for syntax-only conditions, a
syntactic hypothesis match) run next. Then it is stated over the block's start
(`overStart`), the hypothesis match is tried again, and the caller's discharger if given,
otherwise `simp [*, rivet]`. Nothing here unfolds a closed definition. Returns the goal as
stated over the start, under its parameter's tag, if it stays open. -/
private meta def discharge (tactic? : Option Syntax) (goal : MVarId) : TacticM (Option MVarId) := do
  let tag ← goal.getTag
  setGoals [goal]
  evalTactic (← `(tactic| try simp only [rivet]))
  let [reduced] ← getGoals | return none
  if ← closes (← `(tactic| first | rfl | decide +kernel | with_reducible assumption)) reduced then
    return none
  let some (named, rewritten) ← overStart reduced | return none
  named.setTag tag
  if rewritten then
    if ← closes (← `(tactic| with_reducible assumption)) named then return none
  let fallback ← match tactic? with
    | some tactic => pure (⟨tactic⟩ : TSyntax `tactic)
    | none => `(tactic| (simp [*, rivet]; done))
  if ← closes (← `(tactic| ($fallback; done))) named then return none
  return some named

end Step

/--
`rivet_step` executes the instruction at the current address of an
`Ensures image (· = s) Q` goal, using that instruction's contract.

It needs a hypothesis `s.status = .running pc`, where `pc` is a numeral or a
definition that unfolds to one, and continues
with a fresh successor state plus one fact per field: `t.registers = …`,
`t.memory = …`, `t.status = .running next`, and so on.

* **States.** An unnamed successor is inaccessible (`s✝`), and its facts refer to
  the state before it, so each step is cheap. `rivet_step as t` names the
  successor as a checkpoint: its facts, the path conditions, and your hypotheses are
  rewritten in terms of the block's start (the state with no recorded facts, such as
  the `s` the proof began with), through every earlier state, named or not, and those
  states and their facts are cleared. A state one of your hypotheses still mentions
  stays. After a checkpoint the context holds your hypotheses, the start, and `t`
  with its facts. Name states where you want readable facts, such as loop heads.
* **Facts** are inaccessible (`h✝`). Use them with `simp [*]` or `assumption`, or
  retrieve one by statement, e.g. `‹t.memory = _›`. Between checkpoints, prefer
  `simp [*]` to `simp_all`, which rewrites every fact with every other.
* **Side conditions.** The location and instruction evidence are supplied
  directly. Every other side condition is first reduced by the `rivet` simp set:
  register and immediate accesses close, and a memory access becomes
  `permits image.writable a 8#64 = true` with `a` over register reads and a literal size.
  Then `rfl` and `decide` (for syntax-only conditions) and a syntactic hypothesis
  match are tried. A condition still open is stated over the block's start: it is
  rewritten with the facts of every state the tactic introduced, named or not, and
  those states and their facts are dropped from that goal. The match is tried again,
  then the fallback discharger, `simp [*, rivet]`.
  `rivet_step (disch := tac)` replaces the fallback and runs on that goal, so it
  only names the region and proves the bounds:
  `(disch := (apply permits_inside frame <;> bv_omega))`.
  Conditions left unproved remain, in that form, as goals tagged with the contract's
  parameter name (`case writable`, `case readable`, …).
* **Lookup** uses `Fetch.prove`, as `rivet_fetch` does: constant time in the
  program size for programs generated as suffix chains (as by `rivet-import`);
  otherwise the list is searched.
* **Conditional jumps** produce goals tagged `taken` and `fallthrough`, each with
  its path condition as a hypothesis, stated in terms of named states.
* `rivet_step tracking [status, registers, memory]` records only those fields
  (default: all). Later facts that depend on an untracked field are dropped.
-/
syntax (name := rivetStep) "rivet_step" (" (" &"disch" " := " tacticSeq ")")?
  (" as " ident)? (" tracking " "[" ident,* "]")? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (image, old) ← goalParts (← getMainGoal)
  let program := mkApp (mkConst ``Image.program) image
  let (address, pc, location) ← findPc old
  let (instruction, instructionProof) ← fetch program address pc
  let operation := instruction.getArg! 2
  let discharger : Option Syntax := if stx[1].getNumArgs > 0 then some stx[1][3] else none
  let named? : Option Name := if stx[2].getNumArgs > 0 then some stx[2][1].getId else none
  let tracked : List Name :=
    if stx[3].getNumArgs > 0 then (stx[3][2].getSepArgs.map (·.getId)).toList else fields
  for field in tracked do
    unless fields.contains field do throwError "rivet_step: unknown field `{field}`"
  -- 1. The contract, with side conditions as goals; discharge what we can.
  let mut unsolved : Array MVarId := #[]
  let mainGoal ← getMainGoal
  -- Goals left open by earlier steps (unproved side conditions) stay open, after ours.
  let pending := (← getGoals).filter (· != mainGoal)
  let contract : Expr ← do
    let (name, operands) ← contractFor operation
    let (proof, sides) ← instantiate name (#[image, address] ++ operands ++ #[old])
    for side in sides do
      -- Location and instruction evidence are known; no context search is needed.
      match ← side.getTag with
      | `location => side.assign location
      | `code =>
        -- Matching the proof against `InstructionAt program pc ?length op` fills in the length.
        unless ← isDefEq (← side.getType) (← inferType instructionProof) do
          throwError "rivet_step: unexpected instruction at {pc}"
        side.assign instructionProof
      | _ => if let some remaining ← discharge discharger side then unsolved := unsolved.push remaining
    instantiateMVars proof
  -- 2. Continue from a fresh successor: build `Ensures.bind contract (fun next equation => ?_)`
  --    directly, so no term is re-elaborated. Internal names are replaced at the end.
  let next ← mainGoal.withContext do
    let contractType ← whnfR (← inferType contract)
    unless contractType.isAppOfArity ``Ensures 3 do
      throwError "rivet_step: unexpected contract type {contractType}"
    let intermediate := contractType.getArg! 2
    let postcondition := (← whnfR (← mainGoal.getType)).getArg! 2
    let stateType := mkConst ``MachineState
    withLocalDeclD `rivet_next stateType fun successor => do
      withLocalDeclD `rivet_step_equation (intermediate.beta #[successor]) fun equation => do
        let precondition ← withLocalDeclD `state stateType fun state => do
          mkLambdaFVars #[state] (← mkEq state successor)
        let target := mkApp3 (mkConst ``Ensures) image precondition postcondition
        let goal ← mkFreshExprSyntheticOpaqueMVar target (← mainGoal.getTag)
        let continuation ← mkLambdaFVars #[successor, equation] goal
        mainGoal.assign (← mkAppM ``Ensures.bind #[contract, continuation])
        return goal.mvarId!
  setGoals [next]
  let equation := mkIdent `rivet_step_equation
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
  let locations : Array (TSyntax `term) := internal.map (⟨mkIdent ·⟩)
  -- Operand reads and writes go through the `rivet` set's proved equations, never by
  -- unfolding: unfolding computes shift arithmetic on symbolic registers in unary.
  -- They run first, so a register alias is already its parent (`.rax`) when
  -- `MachineState.write` becomes an `if`: its decidability instance keeps whatever
  -- register it was built with, and simp does not rewrite instances.
  evalTactic (← `(tactic| try simp only [rivet] at $locations*))
  evalTactic (← `(tactic| try simp only [MachineState.write,
      MachineState.writeMemory, Operand.width, Width.bits, Width.bytes,
      BitVec.setWidth_eq,
      -- The successor `address + length` reduces to a literal.
      BitVec.reduceOfNat, BitVec.reduceAdd,
      -- A literal shift count is masked and tested for zero (`16 % 32 = 0` is decided).
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
      -- Operand equations, register parents, and addresses as point reads of registers
      -- (`r .rbx - 8#64`), never the whole register file.
      rivet] at $locations*))
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
  -- 5. In each goal: compact if requested, then give the new state and
  --    its facts their final names (yours, or inaccessible).
  let finalName ← match named? with
    | some name => pure name
    | none => mkFreshUserName `s
  let mut finished := #[]
  for (branch, index) in (← getGoals).zipIdx do
    setGoals [branch]
    -- Path conditions are stated in terms of named states right away (the facts of the
    -- unnamed states, and of `old` if it is named); other facts refer to the previous
    -- state until a state is named.
    if isBranch then
      withMainContext do
        let oldNamed := !(← old.fvarId!.getUserName).hasMacroScopes
        let mut states ← (← introducedStates).filterM fun state =>
          return (← state.getUserName).hasMacroScopes
        if oldNamed then states := states.push old.fvarId!
        if let some path := (← getLCtx).findFromUserName? `rivet_fact_path then
          rewriteAt (← notesAbout states) #[path.fvarId]
    if named?.isSome then checkpoint
    -- A path condition that rewrites to `False` closes the goal.
    let some goal := (← getGoals).head? | continue
    let mut goal := goal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        let name ← if fact == `rivet_fact_path then mkFreshUserName `h else noteName
        goal ← goal.rename decl.fvarId name
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    finished := finished.push goal
  setGoals (finished.toList ++ unsolved.toList ++ pending)

end Rivet
end
