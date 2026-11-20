module
public import Rivet.Laws.Instructions
public import Rivet.Laws.Spelling
public import Rivet.Tactics.Fetch
public import Rivet.Tactics.Walk
-- `rivet_step`: executes one instruction of a `Block` goal through its contract.
public meta import Lean

public section
namespace Rivet.Internal
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

private meta def goalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Block 5 do
    throwError "rivet_step: goal is not a `Block`"
  let state := type.getAppArgs[4]!
  unless state.isFVar do throwError "rivet_step: the current state must be a variable"
  return (type.getAppArgs[0]!, state)

private meta def contractFor (operation : Expr) : MetaM (Name × Array Expr) := do
  let args := operation.getAppArgs
  let some ctor := operation.getAppFn.constName?
    | throwError "rivet_step: unrecognized operation {operation}"
  let name ← match ctor with
    | ``Op.nop => pure ``Rivet.Contract.nop | ``Op.movd => pure ``Rivet.Contract.movd
    | ``Op.pshufd => pure ``Rivet.Contract.pshufd | ``Op.loadXmm => pure ``Rivet.Contract.loadXmm
    | ``Op.storeXmm => pure ``Rivet.Contract.storeXmm | ``Op.lea => pure ``Rivet.Contract.lea
    | ``Op.movzx => pure ``Rivet.Contract.movzx | ``Op.movsxd => pure ``Rivet.Contract.movsxd
    | ``Op.mov => pure ``Rivet.Contract.mov | ``Op.shift => pure ``Rivet.Contract.shift
    | ``Op.imul => pure ``Rivet.Contract.imul | ``Op.not => pure ``Rivet.Contract.not
    | ``Op.mul => pure ``Rivet.Contract.mul | ``Op.tzcnt => pure ``Rivet.Contract.tzcnt
    | ``Op.inc => pure ``Rivet.Contract.inc | ``Op.dec => pure ``Rivet.Contract.dec
    | ``Op.jmp => pure ``Rivet.Contract.jmp | ``Op.jcc => pure ``Rivet.Contract.jcc
    | ``Op.setcc => pure ``Rivet.Contract.setcc | ``Op.cmovcc => pure ``Rivet.Contract.cmovcc
    | ``Op.push => pure ``Rivet.Contract.push | ``Op.pop => pure ``Rivet.Contract.pop
    | ``Op.call => pure ``Rivet.Contract.call | ``Op.ret => pure ``Rivet.Contract.ret
    | ``Op.binary =>
      match (← whnf args[0]!).constName? with
      | some ``BinaryOp.add => pure ``Rivet.Contract.add | some ``BinaryOp.sub => pure ``Rivet.Contract.sub
      | some ``BinaryOp.sbb => pure ``Rivet.Contract.sbb | some ``BinaryOp.cmp => pure ``Rivet.Contract.cmp
      | some ``BinaryOp.test => pure ``Rivet.Contract.test | some ``BinaryOp.and => pure ``Rivet.Contract.and
      | some ``BinaryOp.or => pure ``Rivet.Contract.or | _ => pure ``Rivet.Contract.xor
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

private meta def currentPc (state : Expr) : TacticM (Option (Expr × Nat × Expr)) := do
  if let some found ← findPc? state then return found
  let w ← ReadBack.Walk.make (← getMainGoal)
  let status := mkApp (mkConst ``MachineState.status) state
  let result ← w.walk status w.count
  let some address := result.expr.app1? ``ExecutionStatus.running | return none
  let some pc ← Fetch.addressValue? address | return none
  return some (address, pc, ← result.getProof' status)

private meta def fields : List Name :=
  [`registers, `xmmRegisters, `signFlag, `zeroFlag, `carryFlag, `overflowFlag, `memory, `status]

private meta partial def dedupe (e : Expr) (excluded : List (Expr × Expr) := []) : MetaM Simp.Result := do
  let_expr ite _ test _ yes no := e | return { expr := e }
  if let some (_, h) := excluded.find? (·.1 == test) then
    let proof ← mkAppOptM ``ite_eq_right #[test, e.getArg! 2, h, e.getArg! 0, yes, no]
    return ← ({ expr := no, proof? := some proof } : Simp.Result).mkEqTrans (← dedupe no excluded)
  withLocalDeclD `h (mkNot test) fun h => do
    let rest ← dedupe no ((test, h) :: excluded)
    let some proof := rest.proof? | return { expr := e }
    let same := Lean.mkLambda `_ .default test (← mkEqRefl yes)
    let congr ← mkAppOptM ``ite_congr #[e.getArg! 0, test, test, yes, no, yes, rest.expr,
      e.getArg! 2, e.getArg! 2, ← mkEqRefl test, same, ← mkLambdaFVars #[h] proof]
    return { expr := mkApp e.appFn! rest.expr, proof? := some congr }

private meta def dropStates (goal : MVarId) (history : ReadBack.History) : MetaM MVarId := goal.withContext do
  let mut owners : Std.HashMap FVarId FVarId := {}
  for (field, _, proof) in history.equations.toArray do
    owners := owners.insert proof.fvarId! field.appArg!.fvarId!
  for (memory, _, proof) in history.stores.toArray do
    if history.instructions.contains (.fvar memory) then owners := owners.insert proof.fvarId! memory
  let mut notes : Std.HashMap FVarId (Array LocalDecl) := {}
  let mut used := collectFVars {} (← instantiateMVars (← goal.getType))
  let mut subjects := #[]
  for decl in ← getLCtx do
    if (annotation? `Rivet.Step.state decl.type).isSome || history.instructions.contains decl.toExpr then
      subjects := subjects.push decl.fvarId
      continue
    let owner := (decl.type.app3? ``StoredBy).bind (·.1.fvarId?) <|> owners[decl.fvarId]?
    if let some subject := owner then
      notes := notes.insert subject ((notes[subject]?.getD #[]).push decl)
    else
      used := collectFVars used (← instantiateMVars decl.type)
      if let some value := decl.value? then used := collectFVars used (← instantiateMVars value)
  let mut remaining := subjects
  repeat
    let mut unused := #[]
    for subject in remaining.reverse do
      let facts := notes[subject]?.getD #[]
      if used.fvarSet.contains subject || facts.any (fun d => used.fvarSet.contains d.fvarId) then
        for fact in facts do used := collectFVars used (← instantiateMVars fact.type)
      else
        unused := unused.push subject
    if unused.size == remaining.size then break
    remaining := unused
  let drop := remaining.flatMap fun subject =>
    #[subject] ++ (notes[subject]?.getD #[]).map (·.fvarId)
  return (← goal.tryClearMany' drop).1

private meta def checkpoint (w : ReadBack.Walk) (old : Expr) (names : Array Name) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let mut replacements : Array Hypothesis := #[]
  let mut replaced := #[]
  for name in names do
    let some decl := (← getLCtx).findFromUserName? name | continue
    let result : Option (Expr × Expr) ← goal.withContext do
      let id := decl.fvarId
      let type ← instantiateMVars decl.type
      if name == `rivet_fact_path then
        let result ← w.walk type w.count
        let proof ← mkEqMP (← result.getProof' type) (.fvar id)
        return some (result.expr, proof)
      let some (_, lhs, rhs) := type.eq? | throwError "rivet_step: expected a field equation{indentExpr type}"
      let inherited := mkApp lhs.getAppFn old
      let previous := w.history.equations[inherited]?
      let result : Simp.Result ← if rhs == inherited then
          pure <| previous.map (fun (v, h) => { expr := v, proof? := some h }) |>.getD { expr := rhs }
        else if rhs.isLambda then
          lambdaTelescope rhs fun args body => do
            let mut rest := body
            let mut writes := #[]
            while rest.isAppOfArity ``ite 5 do
              let value ← w.walk (rest.getArg! 3) w.count
              writes := writes.push (rest.appFn!.appFn!, value)
              rest := rest.appArg!
            unless rest == mkApp inherited args[0]! do
              throwError "rivet_step: expected the preceding register file at the end of{indentExpr rhs}"
            let mut value : Simp.Result := { expr := rest }
            if let some (chain, equation) := previous then
              value := { expr := chain.beta args, proof? := some (← mkCongrFun equation args[0]!) }
            for (test, written) in writes.reverse do
              value ← Simp.mkCongr (← Simp.mkCongrArg test written) value
            value ← value.mkEqTrans (← dedupe value.expr)
            return { expr := ← mkLambdaFVars args value.expr, proof? := some (← mkAppM ``funext #[← mkLambdaFVars args (← value.getProof' body)]) }
        else w.walk rhs w.count
      if (← ReadBack.isStepState old) && result.expr.containsFVar old.fvarId! then
        throwError "rivet_step: cannot state `{lhs}` without the earlier state `{old}`: {indentExpr result.expr}"
      if result.expr == rhs && !rhs.isLambda then return none
      let proof ← mkEqTrans (.fvar id) (← result.getProof' rhs)
      return some (← mkEq lhs result.expr, proof)
    if let some (type, value) := result then
      replacements := replacements.push { userName := name, type, value }
      replaced := replaced.push decl.fvarId
  let (_, goal) ← goal.assertHypotheses replacements
  let goal ← goal.tryClearMany replaced
  replaceMainGoal [← dropStates goal w.history]

-- A store's result becomes a variable `mₙ`, defined over the block’s start and earlier memories and
-- placed before the new state, so later facts mention the name instead of repeating the stores.
private meta def nameMemory (pc : Nat) (operation : Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let lctx ← getLCtx
  let some fact := lctx.findFromUserName? `rivet_fact_memory | return
  let some (_, _, value) := (← instantiateMVars fact.type).eq? | return
  unless value.isAppOfArity ``Memory.storeBytes 4 do return
  let some next := lctx.findFromUserName? `rivet_next | return
  let name (i : Nat) := Name.mkSimple s!"m{i.toSubscriptString}"
  let mut i := 1
  while lctx.usesUserName (name i) || lctx.usesUserName ((name i).appendAfter "_def") do i := i + 1
  let (reverted, goal) ← goal.revert #[next.fvarId]
  let goal ← goal.assertExt (name i) (mkConst ``Memory) value ((name i).appendAfter "_def")
  let (memory, goal) ← goal.intro1P
  let (definition, goal) ← goal.intro1P
  let goal ← goal.withContext do
    let proof := mkApp3 (mkConst ``StoredBy.intro) (.fvar memory) (mkNatLit pc) operation
    let marker : Hypothesis := { userName := ← mkFreshUserName `mark, type := ← inferType proof, value := proof, kind := .implDetail }
    return (← goal.assertHypotheses #[marker]).2
  let (_, goal) ← goal.introNP reverted.size
  goal.withContext do
    let fact ← getFVarFromUserName `rivet_fact_memory
    let result ← goal.replace fact.fvarId! (← mkEqTrans fact (← mkEqSymm (.fvar definition)))
    replaceMainGoal [result.mvarId]

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

-- A memory access is placed: `r.Has pointer size` for the first region it is placed in that the image
-- grants. It is never left open.
private meta def place (scope : ReadBack.Walk) (pc : Nat) (tag : Name) (goal : MVarId) (writes : Bool) (image pointer size : Expr) :
    TacticM Unit := goal.withContext do
  let at_ := m!"the instruction at 0x{Fetch.hex pc}"
  let result ← scope.walk pointer scope.count
  let address := result.expr
  let known ← scope.places
  let places ← Places.places known address size
  let some (first, _) := places[0]?
    | throwError "rivet_step: the access `{tag}` of {at_} is not placed. State its place before this step, \
        from one you have (`placed.part`) or from its two bounds:\
        {indentExpr (mkApp3 (mkConst ``Region.Has) (mkConst `r) address size)}\nfor the region `r` it lies in; \
        `r.Has p r.length` places every part of `r`. {← Places.named known}{← scope.notes address}"
  for (region, placed) in places do
    let some grant ← Places.grant? known writes image region | continue
    let mut proof := placed
    if let some equal := result.proof? then
      let f ← withLocalDeclD `p (← inferType pointer) fun p =>
        mkLambdaFVars #[p] (mkApp3 (mkConst ``Region.Has) region p size)
      proof ← mkEqMPR (← mkCongrArg f equal) placed
    goal.assign (← mkAppM (if writes then ``Image.Writes.permits else ``Image.Reads.permits) #[grant, proof])
    return
  throwError "rivet_step: the image is not known to grant the access `{tag}` of {at_}: there is no hypothesis\
    {indentExpr (mkApp2 (mkConst (if writes then ``Image.Writes else ``Image.Reads)) image first)}"

private meta def discharge (scope : ReadBack.Walk) (pc : Nat) (goal : MVarId) : TacticM (Option MVarId) := do
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
    place scope pc tag reduced writes image pointer size
    return none
  if ← closes (← `(tactic| first | rfl | decide +kernel | with_reducible assumption)) reduced then return none
  let some named ← scope.readBack reduced | return none
  named.setTag tag
  if ← closes (← `(tactic| with_reducible assumption)) named then return none
  return some named

-- Instantiate the step with symbolic continuations while its binders enclose just one instruction.
-- Their real proofs stay outside those binders, in the caller's local context.
private meta def closeStep (root : MVarId) (goals : Array MVarId) : MetaM Unit := root.withContext do
  let original ← getLCtx
  let mut symbolic ← getMCtx
  let mut binders := #[]
  let mut arguments := #[]
  for goal in goals do
    let (param, type, app, argument) ← goal.withContext do
      let locals := (← getLCtx).getFVars.filter fun x => !original.contains x.fvarId!
      let args ← locals.filterM fun x => return !(← x.fvarId!.isLetVar)
      let param := mkFVar (← mkFreshFVarId)
      return (param, ← mkForallFVars locals (← goal.getType), mkAppN param args,
        ← mkLambdaFVars locals (mkMVar goal))
    symbolic := { symbolic with eAssignment := symbolic.eAssignment.insert goal app }
    binders := binders.push (param, type)
    arguments := arguments.push argument
  let (body, _) := instantiateMVarsCore symbolic (mkMVar root)
  let rule := binders.foldr (init := body) fun (param, type) body =>
    .lam `next type (body.abstract #[param]) .default
  root.assign (mkAppN rule arguments)

end Step

syntax (name := rivetStep) "rivet_step" (" as " ident)? (" if " ident)? : tactic

open Step in
@[tactic rivetStep] meta def Step.evalRivetStep : Tactic := fun stx => withMainContext do
  let (image, old) ← goalParts (← getMainGoal)
  let program := mkApp (mkConst ``Image.program) image
  let some (written, pc, location) ← currentPc old | throwError (← noAddress "rivet_step" old)
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
  let scope ← ReadBack.Walk.make mainGoal
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
        if let some remaining ← discharge scope pc side then unsolved := unsolved.push remaining
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
  let internal := fields.toArray.map fun field => Name.mkSimple s!"rivet_fact_{field}"
  withMainContext do
    let goal ← getMainGoal
    let eqn ← getFVarFromUserName equation.getId
    let mut projections := #[]
    for (field, name) in fields.toArray.zip internal do
      let value ← mkCongrArg (mkConst (`Rivet.MachineState ++ field)) eqn
      projections := projections.push { userName := name, type := ← inferType value, value }
    let (_, goal) ← goal.assertHypotheses projections
    replaceMainGoal [← goal.clear eqn.fvarId!]
  let locations : Array (TSyntax `term) := internal.map (⟨mkIdent ·⟩)
  -- Operand reads and writes go through the `rivet` set's proved equations, never by
  -- unfolding: unfolding computes shift arithmetic on symbolic registers in unary.
  -- They run first, so a register alias is already its parent (`.rax`) when
  -- `MachineState.write` becomes an `if`: its decidability instance keeps whatever
  -- register it was built with, and simp does not rewrite instances.
  evalTactic (← `(tactic| try simp only [rivet] at $locations*))
  -- Then the model's own writes, and the `rivet` set again on what they leave.
  let pendingWrites ← withMainContext do
    locations.filterM fun name => do
      let decl ← (← getFVarFromUserName name.raw.getId).fvarId!.getDecl
      return (decl.type.find? fun e => e.isConstOf ``MachineState.write ||
        e.isConstOf ``MachineState.writeMemory || e.isConstOf ``Width.bits).isSome
  unless pendingWrites.isEmpty do
    evalTactic (← `(tactic| try simp only [MachineState.write, MachineState.writeMemory, Width.bits, rivet]
      at $pendingWrites*))
  -- 4. Conditional jump: two tagged goals, each with its path condition.
  if isBranch then
    let condition ← Term.exprToSyntax operation.getAppArgs[0]!
    let oldStx ← Term.exprToSyntax old
    let status := mkIdent `rivet_fact_status
    let path := mkIdent `rivet_fact_path
    -- The status fact already tests the flags, spelled by the `rivet` set; spell the path
    -- condition the same way to match it.
    evalTactic (← `(tactic| by_cases $path : Condition.holds $condition $oldStx = true <;>
      simp only [rivet, Classical.not_not] at $path:ident <;>
      simp only [$path:ident, rivet] at $status:ident))
  -- Normalize before naming the memory and state.
  let finalName ← match named? with
    | some name => pure name
    | none => mkFreshUserName `s
  let mut finished := #[]
  for (branch, index) in (← getGoals).zipIdx do
    setGoals [branch]
    checkpoint scope old (internal.push `rivet_fact_path)
    nameMemory pc operation
    let mut goal ← getMainGoal
    let lctx ← goal.withContext getLCtx
    if let some decl := lctx.findFromUserName? `rivet_next then
      goal ← goal.rename decl.fvarId finalName
      goal.setFVarType decl.fvarId (mkAnnotation `Rivet.Step.state decl.type)
    for fact in internal do
      if let some decl := lctx.findFromUserName? fact then
        let field := (fact.toString.drop "rivet_fact_".length).toString
        goal ← goal.rename decl.fvarId (← match named? with
          | some state => pure (state.appendAfter s!"_{field}")
          | none => ReadBack.noteName)
    if let (some condition, some decl) := (condition?, lctx.findFromUserName? `rivet_fact_path) then
      goal ← goal.rename decl.fvarId condition
    if isBranch then goal.setTag (if index == 0 then `taken else `fallthrough)
    goal.modifyLCtx fun ctx => ctx.foldl (init := { auxDeclToFullName := ctx.auxDeclToFullName }) LocalContext.addDecl
    finished := finished.push goal
  closeStep mainGoal (finished ++ unsolved)
  setGoals (finished.toList ++ unsolved.toList ++ pending)

syntax (name := rivetStepTo) "rivet_step" &" to " term (" as " ident)? : tactic

-- Steps until the block is at the address, the last step naming its state when asked. A conditional
-- jump on the way stops it, as a bare step does.
open Step in
@[tactic rivetStepTo] meta def Step.evalRivetStepTo : Tactic := fun stx => withMainContext do
  let some target ← Fetch.addressValue? (← Term.elabTermAndSynthesize stx[2] (mkApp (mkConst ``BitVec) (mkNatLit 64)))
    | throwError "rivet_step to: `{stx[2]}` is not an address"
  let named? : Option Ident := if stx[3].getNumArgs > 0 then some ⟨stx[3][1]⟩ else none
  let pcOf : TacticM Nat := withMainContext do
    let (_, state) ← goalParts (← getMainGoal)
    let some (_, pc, _) ← currentPc state | throwError (← noAddress "rivet_step to" state)
    return pc
  if (← pcOf) == target && named?.isSome then
    throwError "rivet_step to: the block is already at 0x{Fetch.hex target}, so no step is named"
  repeat
    if (← pcOf) == target then return
    let saved ← saveState
    evalTactic (← `(tactic| rivet_step))
    if let some name := named? then
      if (← pcOf) == target then
        saved.restore
        evalTactic (← `(tactic| rivet_step as $name))

end Rivet.Internal
end
