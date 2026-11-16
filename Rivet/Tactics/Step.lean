module
public import Rivet.Laws.Instructions
public import Rivet.Laws.Spelling
public import Rivet.Tactics.Fetch
public import Rivet.Tactics.Places
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

-- Marks a state a step named, so later steps know its facts `t_<field>` from yours. The marker is an
-- implementation detail: it is not shown, and tactics skip it.
inductive Introduced {α : Sort u} (x : α) : Prop
  | intro

-- Marks a store's memory `mₙ`, with the instruction that made it, for errors that name the store.
inductive StoredBy (memory : Memory) (address : Nat) (operation : Op) : Prop
  | intro

private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Block 5 do
    throwError "rivet_step: goal is not a `Block`"
  let state := type.getAppArgs[4]!
  unless state.isFVar do throwError "rivet_step: the current state must be a variable"
  return (type.getAppArgs[0]!, state)

-- Where a state is: a hypothesis `state.status = .running address`, or a record's field that says so.
-- The address as written, its value, and the proof.
meta def findPc? (state : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for (proof, part) in ← ReadBack.parts decl.toExpr decl.type do
      let some (_, lhs, rhs) := part.eq? | continue
      unless lhs.isAppOfArity ``MachineState.status 1 && lhs.appArg! == state do continue
      unless rhs.isAppOfArity ``ExecutionStatus.running 1 do continue
      -- A numeral, or a definition such as an imported `entry` that unfolds to one.
      let address := rhs.appArg!
      if let some pc ← Fetch.addressValue? address then return (address, pc, proof)
  return none

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

private meta def isFact (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && decl.userName.toString.startsWith "rivet_fact_"

private meta def mark (goal : MVarId) (proof : Expr) : MetaM MVarId := goal.withContext do
  let (marker, goal) ← (← goal.assert (← mkFreshUserName `mark) (← inferType proof) proof).intro1P
  goal.setFVarKind marker .implDetail
  return goal

private meta def markersOf (subject : FVarId) : MetaM (Array FVarId) := do
  let mut found := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do continue
    let type ← instantiateMVars decl.type
    if (type.isAppOfArity ``Introduced 2 && type.appArg! == .fvar subject) ||
        (type.isAppOfArity ``StoredBy 3 && type.getArg! 0 == .fvar subject) then found := found.push decl.fvarId
  return found

-- A step's fact about a state: hidden for an unnamed state, `t_<field>` for a named one. A call's facts
-- are named as a step's hidden ones.
private meta def noteState? (decl : LocalDecl) : MetaM (Option FVarId) := do
  if decl.isImplementationDetail then return none
  let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | return none
  let some state := ReadBack.fieldOf? lhs | return none
  let some field := lhs.getAppFn.constName? | return none
  if ReadBack.isNote decl then return some state
  unless decl.userName == (← state.getUserName).appendAfter s!"_{field.getString!}" do
    return none
  return if (← markersOf state).isEmpty then none else some state

-- A store's memory name `mₙ`, from its definition `mₙ_def`.
private meta def memoryNamed? (decl : LocalDecl) : MetaM (Option FVarId) := do
  if decl.isImplementationDetail then return none
  let some (_, .fvar memory, _) := (← instantiateMVars decl.type).eq? | return none
  unless decl.userName == (← memory.getUserName).appendAfter "_def" do return none
  return if (← markersOf memory).isEmpty then none else some memory

-- The states with facts: those the steps introduced, and the ends of nested blocks, which stay, since
-- a field their postcondition does not state is stated over them.
private meta def notedStates : MetaM (Array FVarId × Array FVarId) := do
  let mut states := #[]
  let mut ends := #[]
  for decl in ← getLCtx do
    if let some state ← noteState? decl then
      if states.contains state || ends.contains state then continue
      if (← ReadBack.keptBy (.fvar state)).isEmpty then states := states.push state
      else ends := ends.push state
  return (states, ends)

-- States the targets over the block's start, or over the end of the last nested block, through every
-- noted fact.
private meta def restate (goal : MVarId) (targets : Array FVarId) (target : Bool := false) :
    TacticM (Option MVarId) := goal.withContext do
  let mut notes := #[]
  for decl in ← getLCtx do
    if (← noteState? decl).isSome then notes := notes.push decl
  if notes.isEmpty || (targets.isEmpty && !target) then return some goal
  let lemmas ← notes.mapM fun decl => do
    let term ← Term.exprToSyntax (.fvar decl.fvarId)
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let stx ← `(tactic| simp only [$lemmas,*, rivet])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  -- A branch's condition is restated on its own, last: it never closes its arm, even as `False`.
  let path ← targets.filterM fun fact => return (← fact.getDecl).userName == `rivet_fact_path
  -- A fact may stay over the end of a nested block.
  let (some (facts, goal), _) ← simpGoal goal (ctx.setFailIfUnchanged false) simprocs (simplifyTarget := target)
    (fvarIdsToSimp := targets.filter (!path.contains ·)) | return none
  -- A register written twice is tested twice, and the second test can never hold: drop it, and
  -- prove that for each register. Contextual simp would drop it too, but its cost doubles with
  -- each register in the chain. Last fact first, since `replace` renames the facts after it.
  let goal ← facts.foldrM (init := goal) fun fact goal => goal.withContext do
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
  if path.isEmpty then return goal
  goal.withContext do
    let some path := (← getLCtx).findFromUserName? `rivet_fact_path | unreachable!
    let (result, _) ← simp (← instantiateMVars path.type) ctx simprocs
    let proof ← match result.proof? with
      | some equal => mkEqMP equal path.toExpr
      | none => mkExpectedTypeHint path.toExpr result.expr
    return (← goal.replace path.fvarId proof result.expr).mvarId

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
  let (states, ends) ← notedStates
  if states.isEmpty && ends.isEmpty then return
  let mut targets := #[]
  for decl in ← getLCtx do
    unless isFact decl do continue
    let type ← instantiateMVars decl.type
    if (states ++ ends).any (type.containsFVar ·) then targets := targets.push decl.fvarId
  let some goal ← restate (← getMainGoal) targets | replaceMainGoal []
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
  replaceMainGoal (← restate (← getMainGoal) #[before]).toList
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
    replaceMainGoal [← mark goal (mkApp3 (mkConst ``StoredBy.intro) (.fvar memory.get!.fvarId) (mkNatLit pc) operation)]
    return some definition
  let some definition := definition | return
  evalTactic (← `(tactic| replace $fact:ident := Eq.trans $fact (Eq.symm $definition)))

-- Whether the tactic closes the goal. If it does not, nothing it did is kept.
meta def closes (tactic : TSyntax `tactic) (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic tactic
    if (← getGoals).isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

private meta def overStart (goal : MVarId) : TacticM (Option (MVarId × Bool)) := goal.withContext do
  let (states, ends) ← notedStates
  let mut goal := goal
  let rewritten := (states ++ ends).any ((← instantiateMVars (← goal.getType)).containsFVar ·)
  if rewritten then
    let some next ← restate goal #[] (target := true) | return none
    goal := next
  return some (← dropStates goal states, rewritten)

-- A memory access is placed: `r.Has pointer size` for a region the image grants, both hypotheses in
-- scope. It is never left open.
private meta def place (pc : Nat) (tag : Name) (goal : MVarId) (writes : Bool) (image pointer size : Expr) :
    TacticM Unit := goal.withContext do
  let at_ := m!"the instruction at 0x{Fetch.hex pc}"
  let r ← mkFreshExprMVar (mkConst ``Region)
  let placed ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Region.Has) r pointer size) tag
  let granted ← mkFreshExprSyntheticOpaqueMVar
    (mkApp2 (mkConst (if writes then ``Image.Writes else ``Image.Reads)) image r)
  goal.assign (← mkAppM (if writes then ``Image.Writes.permits else ``Image.Reads.permits) #[granted, placed])
  setGoals [placed.mvarId!]
  let some (named, _) ← overStart placed.mvarId! | throwError "rivet_step: unexpected side condition `{tag}` of {at_}"
  named.withContext do
    let_expr Region.Has _ address length := ← instantiateMVars (← named.getType)
      | throwError "rivet_step: unexpected side condition `{tag}` of {at_}"
    let some (region, proof) ← Places.has? r address length
      | throwError "rivet_step: the access `{tag}` of {at_} is not placed. State its place before this step, \
          from one you have (`placed.first`, `placed.part`) or from its two bounds:\
          {indentExpr (mkApp3 (mkConst ``Region.Has) (mkConst `r) address length)}\nfor the region `r` it lies in. \
          {← Places.named}"
    unless ← isDefEq r region do throwError "rivet_step: unexpected side condition `{tag}` of {at_}"
    named.assign proof
    let some grant ← Places.grant? writes image region
      | throwError "rivet_step: the image is not known to grant the access `{tag}` of {at_}: there is no hypothesis\
          {indentExpr (← instantiateMVars (← granted.mvarId!.getType))}"
    granted.mvarId!.assign grant

private meta def discharge (pc : Nat) (goal : MVarId) : TacticM (Option MVarId) := do
  let tag ← goal.getTag
  setGoals [goal]
  evalTactic (← `(tactic| try simp only [rivet]))
  let [reduced] ← getGoals | return none
  let access? ← reduced.withContext do
    let some (_, lhs, _) := (← instantiateMVars (← reduced.getType)).eq? | return none
    let_expr permits permission pointer size := lhs | return none
    if let some image := permission.app1? ``Image.readable then return some (false, image, pointer, size)
    if let some image := permission.app1? ``Image.writable then return some (true, image, pointer, size)
    return none
  if let some (writes, image, pointer, size) := access? then
    place pc tag reduced writes image pointer size
    return none
  if ← closes (← `(tactic| first | rfl | decide +kernel | with_reducible assumption)) reduced then return none
  let some (named, rewritten) ← overStart reduced | return none
  named.setTag tag
  if rewritten then
    if ← closes (← `(tactic| with_reducible assumption)) named then return none
  return some named

end Step

syntax (name := rivetStep) "rivet_step" (" as " ident)? (" if " ident)? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (image, old) ← goalParts (← getMainGoal)
  let program := mkApp (mkConst ``Image.program) image
  let some (written, pc, location) ← findPc? old
    | throwError "rivet_step: no hypothesis `{old}.status = .running <address>`"
  reporting m!"rivet_step, at the instruction at 0x{Fetch.hex pc}" do
  -- An address given by a definition is passed as its value, so the next address is a literal too.
  let (address, location) ← if (← getBitVecValue? written).isSome then pure (written, location) else do
    let address := toExpr (BitVec.ofNat 64 pc)
    let status := mkApp (mkConst ``MachineState.status) old
    pure (address, ← mkExpectedTypeHint location (← mkEq status (mkApp (mkConst ``ExecutionStatus.running) address)))
  let some (instruction, instructionProof) ← Fetch.prove program address pc
    | throwError "rivet_step: no instruction at 0x{Fetch.hex pc}"
  let operation := instruction.getArg! 2
  let named? : Option Name := if stx[1].getNumArgs > 0 then some stx[1][1].getId else none
  let condition? : Option Name := if stx[2].getNumArgs > 0 then some stx[2][1].getId else none
  -- A step that splits the proof in two says so.
  let isBranch := operation.isAppOfArity ``Op.jcc 2
  if isBranch && condition?.isNone then
    throwError "rivet_step: the instruction at 0x{Fetch.hex pc} is a conditional jump. \
      Step it with `rivet_step if h`: it splits the proof in two, `taken` and `fallthrough`, with its \
      condition as `h` in each."
  if let some condition := condition? then
    unless isBranch do
      throwError "rivet_step: `if {condition}` names a branch condition, and the instruction at \
        0x{Fetch.hex pc} is not a conditional jump"
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
      | _ =>
        if let some remaining ← discharge pc side then unsolved := unsolved.push remaining
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
  -- Unpack existential results (the flags an instruction leaves undefined) down to the equation.
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
  -- Then the model's own writes, and the `rivet` set again on what they leave.
  evalTactic (← `(tactic| try simp only [MachineState.write, MachineState.writeMemory, Width.bits, rivet]
    at $locations*))
  nameMemory pc operation
  -- 4. Conditional jump: two tagged goals, each with its path condition.
  if isBranch then
    let condition ← Term.exprToSyntax operation.getAppArgs[0]!
    let oldStx ← Term.exprToSyntax old
    let status := mkIdent `rivet_fact_status
    let path := mkIdent `rivet_fact_path
    -- The status fact already tests the flags, spelled by the `rivet` set; spell the path
    -- condition the same way to match it.
    evalTactic (← `(tactic| by_cases $path : Condition.holds $condition $oldStx = true <;>
      simp only [rivet] at $path:ident <;>
      simp only [$path:ident, rivet] at $status:ident))
  -- 5. In each goal: state the new state over the block's start, drop the old one, then give the new
  --    state and its facts their final names (yours, or inaccessible).
  let finalName ← match named? with
    | some name => pure name
    | none => mkFreshUserName `s
  let mut finished := #[]
  for (branch, index) in (← getGoals).zipIdx do
    setGoals [branch]
    checkpoint
    let mut goal ← getMainGoal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
      if named?.isSome then
        goal ← goal.withContext do mark goal (← mkAppOptM ``Introduced.intro #[none, Expr.fvar decl.fvarId])
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        let field := (fact.toString.drop "rivet_fact_".length).toString
        goal ← goal.rename decl.fvarId (← match named? with
          | some state => pure (state.appendAfter s!"_{field}")
          | none => ReadBack.noteName)
    if let (some condition, some decl) := (condition?, lctx.findFromUserName? `rivet_fact_path) then
      goal ← goal.rename decl.fvarId condition
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    finished := finished.push goal
  setGoals (finished.toList ++ unsolved.toList ++ pending)

syntax (name := rivetStepTo) "rivet_step" &" to " term : tactic

-- Steps until the block is at the address. A conditional jump on the way stops it, as a bare step does.
open Step in
@[tactic rivetStepTo] meta def Step.evalRivetStepTo : Tactic := fun stx => withMainContext do
  let some target ← Fetch.addressValue? (← Term.elabTermAndSynthesize stx[2] (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    | throwError "rivet_step to: `{stx[2]}` is not an address"
  repeat
    let pc ← withMainContext do
      let (_, state) ← goalParts (← getMainGoal)
      let some (_, pc, _) ← findPc? state
        | throwError "rivet_step to: no hypothesis `{state}.status = .running <address>`"
      return pc
    if pc == target then return
    evalTactic (← `(tactic| rivet_step))

end Rivet
end
