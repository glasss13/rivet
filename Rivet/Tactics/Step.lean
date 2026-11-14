module
public import Rivet.Laws.Instructions
public import Rivet.Laws.Spelling
public import Rivet.Tactics.Fetch
-- `rivet_step`: executes one instruction of a `Block` goal through its contract.
public meta import Lean

-- The tactic implementation is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

-- Lean's recursion and heartbeat limits stop a tactic wherever they are reached, and nothing in
-- Rivet catches them on the way. Each tactic says, as they pass, what it was doing.
meta def reporting {α} (doing : MessageData) (tactic : TacticM α) : TacticM α :=
  tryCatchRuntimeEx tactic fun error => do
    if error.isMaxHeartbeat then
      throwError "{doing}: it ran out of heartbeats. This part costs too much: split the block, or give \
        `rivet_arith` only the facts it needs. Raising `maxHeartbeats` hides the cost; it does not remove it."
    if error.isMaxRecDepth then throwError "{doing}: it reached Lean's recursion limit."
    throw error

namespace Step

universe u

-- Marks a state or memory the step introduced, so later steps know the facts named after it
-- from yours. The marker is an implementation detail: it is not shown, and tactics skip it.
inductive Introduced {α : Sort u} (x : α) : Prop
  | intro

-- Which instruction made a store's memory, for errors that name the store.
inductive StoredBy (memory : Memory) (address : Nat) (operation : Op) : Prop
  | intro

private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Block 5 do
    throwError "rivet_step: goal is not a `Block`"
  let state := type.getAppArgs[4]!
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
    | ``Op.mul => pure ``Rivet.mul | ``Op.tzcnt => pure ``Rivet.tzcnt
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
  [`registers, `xmmRegisters, `signFlag, `zeroFlag, `carryFlag, `overflowFlag, `memory, `status]

private meta def noteModule : Name := `Rivet.Step.note

-- Path conditions get a name of their own, so later checkpoints know them from the user's.
private meta def pathModule : Name := `Rivet.Step.path

private meta def markModule : Name := `Rivet.Step.mark

private meta def ownName (module : Name) : CoreM Name := do
  return { extractMacroScopes (← mkFreshUserName `h) with ctx := module }.review

private meta def owned (module : Name) (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.hasMacroScopes &&
    (extractMacroScopes decl.userName).ctx == module

private meta def isFact (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.toString.startsWith "rivet_fact_"

private meta def markerOf? (subject : FVarId) : MetaM (Option FVarId) := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do continue
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Introduced 2 && type.appArg! == .fvar subject then return some decl.fvarId
  return none

private meta def hide (goal : MVarId) (proof : Expr) : MetaM MVarId := goal.withContext do
  let (marker, goal) ← (← goal.assert (← ownName markModule) (← inferType proof) proof).intro1P
  goal.setFVarKind marker .implDetail
  return goal

private meta def mark (goal : MVarId) (subject : FVarId) : MetaM MVarId := goal.withContext do
  hide goal (← mkAppOptM ``Introduced.intro #[none, Expr.fvar subject])

private meta def markersOf (subject : FVarId) : MetaM (Array FVarId) := do
  let mut found := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do continue
    let type ← instantiateMVars decl.type
    if (type.isAppOfArity ``Introduced 2 && type.appArg! == .fvar subject) ||
        (type.isAppOfArity ``StoredBy 3 && type.getArg! 0 == .fvar subject) then found := found.push decl.fvarId
  return found

-- A step's fact about a state: hidden for an unnamed state, `t_<field>` for a named one.
private meta def noteState? (decl : LocalDecl) : MetaM (Option FVarId) := do
  if decl.isImplementationDetail then return none
  let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | return none
  unless lhs.isApp && lhs.getAppNumArgs == 1 do return none
  let some field := lhs.getAppFn.constName? | return none
  unless field.getPrefix == ``MachineState do return none
  let .fvar state := lhs.appArg! | return none
  if owned noteModule decl then return some state
  unless decl.userName == (← state.getUserName).appendAfter s!"_{field.getString!}" do
    return none
  return if (← markerOf? state).isSome then some state else none

-- A store's memory name `mₙ`, from its definition `mₙ_def`.
private meta def memoryNamed? (decl : LocalDecl) : MetaM (Option FVarId) := do
  if decl.isImplementationDetail then return none
  let some (_, .fvar memory, _) := (← instantiateMVars decl.type).eq? | return none
  unless decl.userName == (← memory.getUserName).appendAfter "_def" do return none
  return if (← markerOf? memory).isSome then some memory else none

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
  let stx ← `(tactic| simp only [$lemmas,*, reduceCtorEq, ↓reduceIte, rivet, Nat.reduceLeDiff,
    Nat.reduceAdd, Nat.reduceSub, BitVec.reduceSetWidth, BitVec.reduceEq])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let (some (facts, goal), _) ← simpGoal goal ctx simprocs (simplifyTarget := target)
    (fvarIdsToSimp := targets) | return none
  -- A register written twice is tested twice, and the second test can never hold: drop it, and
  -- prove that for each register. Contextual simp would drop it too, but its cost doubles with
  -- each register in the chain. Last fact first, since `replace` renames the facts after it.
  some <$> facts.foldrM (init := goal) fun fact goal => goal.withContext do
    let some (_, _, function) := (← instantiateMVars (← fact.getType)).eq? | return goal
    let .lam binder domain chain info := function | return goal
    let mut kept := #[]
    let mut tested := #[]
    let mut rest := chain
    repeat
      let_expr ite _ test _ _ next := rest | break
      let_expr Eq _ argument register := test | break
      unless argument == .bvar 0 do break
      unless tested.contains register do kept := kept.push rest.appFn!
      tested := tested.push register
      rest := next
    if kept.size == tested.size then return goal
    let same ← mkFreshExprMVar (← mkEq function (.lam binder domain (kept.foldr mkApp rest) info))
    discard <| Tactic.run same.mvarId! do
      evalTactic (← `(tactic| funext r; cases r <;> simp only [reduceCtorEq, ↓reduceIte]))
    return (← goal.replace fact (← mkEqTrans (.fvar fact) same)).mvarId

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
  let dropped := subjects.filter (!kept.contains ·)
  let markers ← dropped.flatMapM markersOf
  let goal ← goal.tryClearMany ((notes.filter (!kept.contains ·.1)).map (·.2.fvarId))
  let goal ← goal.tryClearMany markers
  goal.tryClearMany dropped

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
private meta def nameMemory (pc : Nat) (operation : Expr) : TacticM Unit := do
  let fact := mkIdent `rivet_fact_memory
  let stored : TacticM (Option (FVarId × Expr)) := withMainContext do
    let some decl := (← getLCtx).findFromUserName? fact.getId | return none
    let some (_, _, value) := (← instantiateMVars decl.type).eq? | return none
    return if value.isAppOfArity ``MachineState.memory 1 then none else some (decl.fvarId, value)
  let some (before, _) ← stored | return
  replaceMainGoal (← restate (← getMainGoal) (← withMainContext introducedStates) #[before]).toList
  let some (_, value) ← stored | return
  let definition ← withMainContext do
    let lctx ← getLCtx
    let some next := lctx.findFromUserName? `rivet_next | return none
    let name (index : Nat) := Name.mkSimple s!"m{index.toSubscriptString}"
    let mut index := 1 + (← lctx.foldlM (init := 0) fun count decl =>
      return if (← memoryNamed? decl).isSome then count + 1 else count)
    while lctx.usesUserName (name index) || lctx.usesUserName ((name index).appendAfter "_def") do
      index := index + 1
    let definition := mkIdent ((name index).appendAfter "_def")
    let (reverted, goal) ← (← getMainGoal).revert #[next.fvarId]
    replaceMainGoal [goal]
    evalTactic (← `(tactic| obtain ⟨$(mkIdent (name index)), $definition⟩ :
      ∃ memory : Memory, memory = $(← Term.exprToSyntax value) := ⟨_, rfl⟩))
    let (_, goal) ← (← getMainGoal).introNP reverted.size
    let memory ← goal.withContext do return (← getLCtx).findFromUserName? (name index)
    let goal ← mark goal memory.get!.fvarId
    replaceMainGoal [← hide goal (mkApp3 (mkConst ``StoredBy.intro) (.fvar memory.get!.fvarId) (mkNatLit pc) operation)]
    return some definition
  let some definition := definition | return
  evalTactic (← `(tactic| replace $fact:ident := Eq.trans $fact (Eq.symm $definition)))

private meta def attempt (tactic : TSyntax `tactic) (goal : MVarId) (runtime := false) :
    TacticM (Option MessageData) := do
  let saved ← saveState
  let logged := (← Core.getMessageLog).toList.length
  let body : TacticM (Option MessageData) := do
    setGoals [goal]
    evalTactic tactic
    let remaining ← getGoals
    if remaining.isEmpty then return none
    -- `restore` below discards these goals; the message keeps the context they need.
    return some (← addMessageContext m!"it left{indentD (goalsToMessageData remaining)}")
  -- A tactic that aborts, as `t <;> grind` does, has already logged its error; `restore` would drop it.
  let handler (error : Exception) : TacticM (Option MessageData) := do
    let errors := ((← Core.getMessageLog).toList.drop logged).filter (·.severity == .error)
    let reason := match error, errors with
      | .internal .., _ :: _ => MessageData.joinSep (errors.map (·.data)) Format.line
      | _, _ => error.toMessageData
    return some m!"it failed with{indentD reason}"
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
  (" as " ident)? (" if " ident)? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (image, old) ← goalParts (← getMainGoal)
  let program := mkApp (mkConst ``Image.program) image
  let (written, pc, location) ← findPc old
  reporting m!"rivet_step, at the instruction at 0x{String.ofList (Nat.toDigits 16 pc)}" do
  -- An address given by a definition is passed as its value, so the next address is a literal too.
  let (address, location) ← if (← getBitVecValue? written).isSome then pure (written, location) else do
    let address := toExpr (BitVec.ofNat 64 pc)
    let status := mkApp (mkConst ``MachineState.status) old
    pure (address, ← mkExpectedTypeHint location (← mkEq status (mkApp (mkConst ``ExecutionStatus.running) address)))
  let (instruction, instructionProof) ← fetch program address pc
  let operation := instruction.getArg! 2
  let discharger : Option Syntax := if stx[1].getNumArgs > 0 then some stx[1][3] else none
  let named? : Option Name := if stx[2].getNumArgs > 0 then some stx[2][1].getId else none
  let condition? : Option Name := if stx[3].getNumArgs > 0 then some stx[3][1].getId else none
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
  -- 2. Continue from a fresh successor: build `Block.then contract (fun next _ equation => ?_)`
  --    directly, so no term is re-elaborated. Internal names are replaced at the end. The
  --    contract's change is dropped: the equation says more.
  let next ← mainGoal.withContext do
    let contractType ← whnfR (← inferType contract)
    unless contractType.isAppOfArity ``Block 5 do
      throwError "rivet_step: unexpected contract type {contractType}"
    let intermediate := contractType.getArg! 3
    let goalArgs := (← whnfR (← mainGoal.getType)).getAppArgs
    let stateType := mkConst ``MachineState
    withLocalDeclD `rivet_next stateType fun successor => do
      let kept := mkApp3 (mkConst ``MachineState.Except) successor (contractType.getArg! 1) (contractType.getArg! 2)
      withLocalDeclD `rivet_kept kept fun kept => do
      withLocalDeclD `rivet_step_equation (intermediate.beta #[successor]) fun equation => do
        let target := mkApp5 (mkConst ``Block) image goalArgs[1]! goalArgs[2]! goalArgs[3]! successor
        let goal ← mkFreshExprSyntheticOpaqueMVar target (← mainGoal.getTag)
        let continuation ← mkLambdaFVars #[successor, kept, equation] goal
        mainGoal.assign (← mkAppM ``Block.then #[contract, continuation])
        return (← goal.mvarId!.clear kept.fvarId!)
  setGoals [next]
  let equation := mkIdent `rivet_step_equation
  -- Unpack existential results (IMUL's unconstrained flags) down to the equation.
  repeat
    let isExists ← withMainContext do
      let some decl := (← getLCtx).findFromUserName? equation.getId | return false
      return (← whnfR (← instantiateMVars decl.type)).isAppOfArity ``Exists 2
    unless isExists do break
    evalTactic (← `(tactic| obtain ⟨_, $equation⟩ := $equation))
  -- 3. One fact per field, normalized.
  let mut internal : Array Name := #[]
  for field in fields do
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
  nameMemory pc operation
  -- 4. Conditional jump: two tagged goals, each with its path condition.
  let isBranch := operation.isAppOfArity ``Op.jcc 2
  if let some condition := condition? then
    unless isBranch do
      throwError "rivet_step: `if {condition}` names a branch condition, and the instruction at \
        0x{String.ofList (Nat.toDigits 16 pc)} is not a conditional jump"
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
  -- 5. In each goal: state the new state over the block's start, drop the old one, then give the new
  --    state and its facts their final names (yours, or inaccessible).
  let finalName ← match named? with
    | some name => pure name
    | none => mkFreshUserName `s
  let mut finished := #[]
  for (branch, index) in (← getGoals).zipIdx do
    setGoals [branch]
    checkpoint
    -- A path condition that rewrites to `False` closes the goal.
    let some goal := (← getGoals).head? | continue
    let mut goal := goal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
      if named?.isSome then goal ← mark goal decl.fvarId
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        let field := (fact.toString.drop "rivet_fact_".length).toString
        let name ← match fact == `rivet_fact_path, condition?, named? with
          | true, some condition, _ => pure condition
          | true, none, _ => ownName pathModule
          | false, _, some state => pure (state.appendAfter s!"_{field}")
          | false, _, none => ownName noteModule
        goal ← goal.rename decl.fvarId name
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    finished := finished.push goal
  setGoals (finished.toList ++ unsolved.toList ++ pending)

end Rivet
end
