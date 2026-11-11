module
public import Rivet.Laws.Instructions
public import Rivet.Laws.Spelling
public import Rivet.Tactics.Fetch
-- `rivet_step`: executes one instruction of an `Ensures` goal through its contract.
public meta import Lean

-- The tactic implementation is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace Step

private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Ensures 3 do
    throwError "rivet_step: goal is not `Ensures image s Q`"
  let state := type.getAppArgs[1]!
  unless state.isFVar do throwError "rivet_step: the current state must be a variable"
  return (type.getAppArgs[0]!, state)

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

private meta def fetch (program address : Expr) (pc : Nat) : MetaM (Expr × Expr) := do
  let some found ← Fetch.prove program address pc
    | throwError "rivet_step: no instruction at address {pc}"
  return found

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

private meta def instantiate (name : Name) (explicit : Array Expr) : MetaM (Expr × Array MVarId) := do
  let mut proof ← mkConstWithFreshMVarLevels name
  let mut type ← inferType proof
  let mut remaining := explicit.toList
  let mut sides : Array MVarId := #[]
  repeat
    let .forallE binder domain body info := type | break
    let mut argument := domain
    if let some default := domain.getOptParamDefault? then
      -- A contract's `width` defaults to a `match` on its operand; pass the width it names.
      argument ← whnfD default
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

private meta def fields : List Name :=
  [`registers, `xmmRegisters, `signFlag, `zeroFlag, `carryFlag, `memory, `status]

private meta def noteModule : Name := `Rivet.Step.note

-- Path conditions get a name of their own, so later checkpoints know them from the user's.
private meta def pathModule : Name := `Rivet.Step.path

-- A memory name's defining fact gets a name of its own, so steps know the name from the user's.
private meta def memoryModule : Name := `Rivet.Step.memory

private meta def ownName (module : Name) : CoreM Name := do
  return { extractMacroScopes (← mkFreshUserName `h) with ctx := module }.review

private meta def owned (module : Name) (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.hasMacroScopes &&
    (extractMacroScopes decl.userName).ctx == module

private meta def isFact (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.toString.startsWith "rivet_fact_"

private meta def noteState? (decl : LocalDecl) : MetaM (Option FVarId) := do
  unless owned noteModule decl do return none
  let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | return none
  unless lhs.isApp && lhs.getAppNumArgs == 1 &&
      (lhs.getAppFn.constName?.map (·.getPrefix == ``MachineState)).getD false do return none
  let .fvar state := lhs.appArg! | return none
  return some state

private meta def memoryNamed? (decl : LocalDecl) : MetaM (Option FVarId) := do
  unless owned memoryModule decl do return none
  let some (_, .fvar memory, _) := (← instantiateMVars decl.type).eq? | return none
  return some memory

private meta def notesAbout (states : Array FVarId) : MetaM (Array LocalDecl) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if let some state ← noteState? decl then
      if states.contains state then found := found.push decl
  return found

private meta def introducedStates : MetaM (Array FVarId) := do
  let mut states := #[]
  for decl in ← getLCtx do
    if let some state ← noteState? decl then
      unless states.contains state do states := states.push state
  return states

private meta def restate (goal : MVarId) (states : Array FVarId) (targets : Array FVarId)
    (target : Bool := false) : TacticM (Option MVarId) := goal.withContext do
  let facts ← notesAbout states
  if facts.isEmpty || (targets.isEmpty && !target) then return some goal
  let lemmas ← facts.mapM fun decl => do
    let term ← Term.exprToSyntax (.fvar decl.fvarId)
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let stx ← if target then
      `(tactic| simp only [$lemmas,*, reduceCtorEq, ↓reduceIte, rivet, Nat.reduceLeDiff,
        Nat.reduceAdd, Nat.reduceSub, BitVec.reduceSetWidth, BitVec.reduceEq])
    else
      -- `+contextual` drops the branch an earlier write to the same register leaves under
      -- `¬ register = .rsp`; without it every push and pop adds a dead `if`.
      `(tactic| simp +contextual only [$lemmas,*, reduceCtorEq, ↓reduceIte,
        rivet, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub, BitVec.reduceSetWidth, BitVec.reduceEq])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let (result?, _) ← simpGoal goal ctx simprocs (simplifyTarget := target)
    (fvarIdsToSimp := targets)
  return result?.map (·.2)

-- Drops the given states and every memory name that nothing else mentions, with their facts.
private meta def dropStates (goal : MVarId) (states : Array FVarId) : MetaM MVarId :=
    goal.withContext do
  let mut subjects := states
  let mut uses : Array Expr := #[← instantiateMVars (← goal.getType)]
  let mut notes : Array (FVarId × LocalDecl) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || states.contains decl.fvarId then continue
    if let some memory ← memoryNamed? decl then
      subjects := subjects.push memory
      notes := notes.push (memory, decl)
      continue
    match ← noteState? decl with
    | some state => if states.contains state then notes := notes.push (state, decl)
                    else uses := uses.push (← instantiateMVars decl.type)
    | none => uses := uses.push (← instantiateMVars decl.type)
  if subjects.isEmpty then return goal
  let mut kept : Array FVarId := #[]
  let mut grown := true
  while grown do
    grown := false
    for subject in subjects do
      if kept.contains subject || !uses.any (·.containsFVar subject) then continue
      kept := kept.push subject
      grown := true
      for (about, decl) in notes do
        if about == subject then uses := uses.push (← instantiateMVars decl.type)
  let goal ← goal.tryClearMany ((notes.filter (!kept.contains ·.1)).map (·.2.fvarId))
  goal.tryClearMany (subjects.filter (!kept.contains ·))

private meta def checkpoint : TacticM Unit := withMainContext do
  let states ← introducedStates
  if states.isEmpty then return
  let mut targets := #[]
  for decl in ← getLCtx do
    unless isFact decl || owned pathModule decl do continue
    let type ← instantiateMVars decl.type
    if states.any (type.containsFVar ·) then targets := targets.push decl.fvarId
  let some goal ← restate (← getMainGoal) states targets | replaceMainGoal []
  goal.withContext do
    for decl in ← getLCtx do
      let definesMemory := (← memoryNamed? decl).isSome
      unless (isFact decl && decl.userName != `rivet_fact_path) || definesMemory do continue
      let type ← instantiateMVars decl.type
      let some state := states.find? (type.containsFVar ·) | continue
      let field :=
        if definesMemory then "memory" else (decl.userName.toString.drop "rivet_fact_".length).toString
      let read? := type.find? fun e =>
        e.getAppNumArgs == 1 && e.appArg! == .fvar state &&
          (e.getAppFn.constName?.map (·.getPrefix == ``MachineState)).getD false
      let why := match read? with
        | some read => m!"there is no fact `{read} = …` to restate `{read}` with"
        | none => m!"it mentions `{Expr.fvar state}` other than through one of its fields"
      throwError "rivet_step: the new state's `{field}` cannot be stated without the earlier \
        state `{Expr.fvar state}`: {why}.{indentExpr type}"
  replaceMainGoal [← dropStates goal states]

-- A store's result becomes a variable `mₙ`, defined over the start state and earlier names and
-- placed before the new state, so later facts mention the name instead of repeating the stores.
private meta def nameMemory : TacticM Unit := do
  let fact := mkIdent `rivet_fact_memory
  let stored : TacticM (Option (FVarId × Expr)) := withMainContext do
    let some decl := (← getLCtx).findFromUserName? fact.getId | return none
    let some (_, _, value) := (← instantiateMVars decl.type).eq? | return none
    return if value.isAppOfArity ``MachineState.memory 1 then none else some (decl.fvarId, value)
  let some (before, _) ← stored | return
  replaceMainGoal (← restate (← getMainGoal) (← withMainContext introducedStates) #[before]).toList
  let some (_, value) ← stored | return
  let definition := mkIdent (← ownName memoryModule)
  withMainContext do
    let lctx ← getLCtx
    let some next := lctx.findFromUserName? `rivet_next | return
    let name (index : Nat) := Name.mkSimple s!"m{index.toSubscriptString}"
    let mut index := 1 + (← lctx.foldlM (init := 0) fun count decl =>
      return if (← memoryNamed? decl).isSome then count + 1 else count)
    while lctx.usesUserName (name index) do index := index + 1
    let (reverted, goal) ← (← getMainGoal).revert #[next.fvarId]
    replaceMainGoal [goal]
    evalTactic (← `(tactic| obtain ⟨$(mkIdent (name index)), $definition⟩ :
      ∃ memory : Memory, memory = $(← Term.exprToSyntax value) := ⟨_, rfl⟩))
    let (_, goal) ← (← getMainGoal).introNP reverted.size
    replaceMainGoal [goal]
  evalTactic (← `(tactic| replace $fact:ident := Eq.trans $fact (Eq.symm $definition)))

private meta def attempt (tactic : TSyntax `tactic) (goal : MVarId) (runtime := false) :
    TacticM (Option MessageData) := do
  let saved ← saveState
  let body : TacticM (Option MessageData) := do
    setGoals [goal]
    evalTactic tactic
    let remaining ← getGoals
    if remaining.isEmpty then return none
    -- `restore` below discards these goals; the message keeps the context they need.
    return some (← addMessageContext m!"it left{indentD (goalsToMessageData remaining)}")
  let handler (error : Exception) : TacticM (Option MessageData) :=
    pure (some m!"it failed with{indentD error.toMessageData}")
  let failure ← if runtime then tryCatchRuntimeEx body handler else tryCatch body handler
  if failure.isSome then saved.restore
  return failure

private meta def closes (tactic : TSyntax `tactic) (goal : MVarId) : TacticM Bool :=
  return (← attempt tactic goal).isNone

private meta def overStart (goal : MVarId) : TacticM (Option (MVarId × Bool)) := goal.withContext do
  let states ← introducedStates
  let mut goal := goal
  let rewritten := states.any ((← instantiateMVars (← goal.getType)).containsFVar ·)
  if rewritten then
    let some next ← restate goal states #[] (target := true) | return none
    goal := next
  return some (← dropStates goal states, rewritten)

private meta def discharge (pc : Nat) (tactic? : Option Syntax) (goal : MVarId) :
    TacticM (Option MVarId) := do
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
  match tactic? with
  | some tactic =>
    let some failure ← attempt ⟨tactic⟩ named (runtime := true) | return none
    throwError "rivet_step: `disch` did not prove the side condition `{tag}` of the \
      instruction at 0x{String.ofList (Nat.toDigits 16 pc)}: {failure}\nThe side condition, as `disch` saw it:\
      {indentD (MessageData.ofGoal named)}"
  | none =>
    if ← closes (← `(tactic| (simp [*, rivet]; done))) named then return none
    return some named

end Step

syntax (name := rivetStep) "rivet_step" (" (" &"disch" " := " tacticSeq ")")?
  (" as " ident)? (" tracking " "[" ident,* "]")? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (image, old) ← goalParts (← getMainGoal)
  let program := mkApp (mkConst ``Image.program) image
  let (written, pc, location) ← findPc old
  -- An address given by a definition is passed as its value, so the next address is a literal too.
  let (address, location) ← if (← getBitVecValue? written).isSome then pure (written, location) else do
    let address := toExpr (BitVec.ofNat 64 pc)
    let status := mkApp (mkConst ``MachineState.status) old
    pure (address, ← mkExpectedTypeHint location (← mkEq status (mkApp (mkConst ``ExecutionStatus.running) address)))
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
      | _ => if let some remaining ← discharge pc discharger side then unsolved := unsolved.push remaining
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
        let target := mkApp3 (mkConst ``Ensures) image successor postcondition
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
      MachineState.writeMemory, Width.bits,
      -- The successor `address + length` reduces to a literal.
      BitVec.reduceOfNat, BitVec.reduceAdd,
      -- A literal shift count is masked and tested for zero (`16 % 32 = 0` is decided).
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
      -- Literal comparisons the `rivet` set's rules need or leave: `8 ≤ 56`, `1 = 0`.
      Nat.reduceLeDiff, Nat.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceEq,
      -- Literal operands as numbers: PSHUFD's lane offsets, IMUL's immediate.
      Nat.reduceMul, Nat.reduceDiv, Nat.reducePow, BitVec.reduceToInt,
      -- A condition as the flags it tests.
      Condition.holds,
      -- Operand equations, register parents, and addresses as point reads of registers
      -- (`r .rbx - 8#64`), never the whole register file.
      rivet] at $locations*))
  nameMemory
  -- 4. Conditional jump: two tagged goals, each with its path condition.
  let isBranch := operation.isAppOfArity ``Op.jcc 2 && tracked.contains `status
  if isBranch then
    let condition ← Term.exprToSyntax operation.getAppArgs[0]!
    let oldStx ← Term.exprToSyntax old
    let status := mkIdent `rivet_fact_status
    let path := mkIdent `rivet_fact_path
    -- The status fact already tests the flags, spelled by the `rivet` set; spell the path
    -- condition the same way to match it.
    evalTactic (← `(tactic| by_cases $path : Condition.holds $condition $oldStx = true <;>
      simp only [Condition.holds, rivet] at $path:ident <;>
      simp only [$path:ident, ↓reduceIte, rivet] at $status:ident))
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
          replaceMainGoal (← restate (← getMainGoal) states #[path.fvarId]).toList
    if named?.isSome then checkpoint
    -- A path condition that rewrites to `False` closes the goal.
    let some goal := (← getGoals).head? | continue
    let mut goal := goal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        let name ← ownName (if fact == `rivet_fact_path then pathModule else noteModule)
        goal ← goal.rename decl.fvarId name
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    finished := finished.push goal
  setGoals (finished.toList ++ unsolved.toList ++ pending)

end Rivet
end
