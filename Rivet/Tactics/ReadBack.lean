module
public import Rivet.Laws.Block
public import Rivet.Tactics.Step
public import Rivet.Tactics.Arith
public meta import Lean
-- The read-back: every value of a later state, read back to the block's start. `rivet_close` closes a
-- goal that, read that way, is a hypothesis, has two equal sides, or follows by `rivet_arith`.
public section
namespace Rivet
open Lean Meta Elab Tactic

theorem MachineState.Except.readBytes {t s : MachineState} {c : Changes} (same : t.Except s c)
    (address : BitVec 64) (size : Nat) (away : c.Misses address.toNat (address.toNat + size))
    (fits : address.toNat + size ≤ 2^64) :
    Rivet.readBytes t.memory address size = Rivet.readBytes s.memory address size :=
  readBytes_congr (fits := fits) fun other _ _ => same.sameMemory other fun range inside => by
    have := away range inside
    omega

namespace ReadBack

meta def opens (type : Expr) : MetaM Bool := do
  let some name := type.getAppFn.constName? | return false
  takesState name

-- What a fact says, part by part: conjuncts, and the fields or body of what `takesState` opens.
meta partial def parts (proof type : Expr) : MetaM (Array (Expr × Expr)) := do
  let type := (← instantiateMVars type).headBeta
  if let some (left, right) := type.and? then
    return (← parts (← mkAppM ``And.left #[proof]) left) ++ (← parts (← mkAppM ``And.right #[proof]) right)
  if ← opens type then
    if isStructure (← getEnv) type.getAppFn.constName! then
      let mut found := #[]
      for field in getStructureFields (← getEnv) type.getAppFn.constName! do
        let part ← mkProjection proof field
        found := found ++ (← parts part (← inferType part))
      return found
    if let some unfolded ← unfoldDefinition? type then return ← parts proof unfolded.headBeta
  return #[(proof, type)]

-- A bound the read-back needs, from the hypotheses in scope.
meta def arith (type : Expr) : MetaM (Except MessageData Expr) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let saved ← Meta.saveState
  try
    discard <| (Tactic.run goal.mvarId! do evalTactic (← `(tactic| rivet_arith))).run'
    return .ok (← instantiateMVars goal)
  catch error =>
    saved.restore
    return .error (← addMessageContext m!"The bound{indentExpr type}\nis not proved. {error.toMessageData}")

-- A state by its name, or by where it is when no step named it.
meta def describe (state : Expr) : MetaM MessageData := do
  if let some id := state.fvarId? then
    unless ((← getLCtx).get! id).userName.hasMacroScopes do return m!"`{state}`"
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? | continue
    unless lhs.isAppOfArity ``MachineState.status 1 && lhs.appArg! == state do continue
    let some address := rhs.app1? ``ExecutionStatus.running | continue
    let value? ← match ← getBitVecValue? address with
      | some ⟨_, value⟩ => pure (some value.toNat)
      | none => getNatValue? address
    if let some value := value? then return m!"the state at 0x{String.ofList (Nat.toDigits 16 value)}"
  return m!"an unnamed state"

meta def showRange (low high : Expr) : MessageData := m!"[{low}, {high})"

-- `c.Misses low high`, range by range.
meta def misses (c low high : Expr) : MetaM (Except MessageData Expr) := do
  let ranges ← changedRanges c
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  let motive ← withLocalDeclD `range pairType fun range => do
    mkLambdaFVars #[range] (mkOr (← mkAppM ``LE.le #[high, ← mkAppM ``Prod.fst #[range]])
      (← mkAppM ``LE.le #[← mkAppM ``Prod.snd #[range], low]))
  let mut proof ← mkAppOptM ``List.forall_mem_nil #[pairType, motive]
  let mut rest ← mkListLit pairType []
  for (range, changedLow, changedHigh) in ranges.reverse do
    match ← arith (mkOr (← mkAppM ``LE.le #[high, changedLow]) (← mkAppM ``LE.le #[changedHigh, low])) with
    | .error why => return .error m!"{showRange low high} is not shown to miss the range \
        {showRange changedLow changedHigh} it may change.\n{why}"
    | .ok head =>
      proof ← mkAppM ``Iff.mpr #[← mkAppOptM ``List.forall_mem_cons #[pairType, motive, range, rest],
        ← mkAppM ``And.intro #[← mkExpectedTypeHint head (motive.beta #[range]), proof]]
      rest ← mkAppM ``List.cons #[range, rest]
  return .ok (← mkExpectedTypeHint proof (← mkAppM ``Changes.Misses #[c, low, high]))

-- The instruction that made a store's memory.
meta def storedBy (memory : FVarId) : MetaM MessageData := do
  for decl in ← getLCtx do
    let_expr Step.StoredBy stored address operation := ← instantiateMVars decl.type | continue
    if stored == .fvar memory then
      let some address ← getNatValue? address | continue
      return m!" by `{operation}` at 0x{String.ofList (Nat.toDigits 16 address)}"
  return m!""

structure Stop where
  read : Expr
  reason : MessageData

-- Reads `size` bytes at `address` (one byte, `memory address`, without `size`) back through the
-- stores and the nested blocks, to the earliest memory it is the same in. A store the read misses is
-- passed; a store that wrote all of it gives the bytes stored; a nested block whose change the read
-- misses is passed. Returns the read there, a proof, and where it stopped short of a start.
-- A store's definition is followed here, one read at a time, and never rewritten with: the bytes a
-- store writes mention earlier memories, and expanding them all is exponential.
meta partial def walk (memory address : Expr) (size? fits? : Option Expr) (name? : Option FVarId := none) :
    MetaM (Expr × Option Expr × Option Stop) := do
  let read (memory : Expr) : Expr := match size? with
    | some size => mkApp3 (mkConst ``readBytes) memory address size
    | none => mkApp memory address
  let here := read memory
  let low ← mkAppM ``BitVec.toNat #[address]
  let high ← mkAppM ``HAdd.hAdd #[low, size?.getD (mkNatLit 1)]
  let next (earlier step : Expr) (name? : Option FVarId := none) : MetaM (Expr × Option Expr × Option Stop) := do
    let (final, rest?, stop?) ← walk earlier address size? fits? name?
    let proof ← match rest? with
      | some rest => mkEqTrans step rest
      | none => pure step
    return (final, some proof, stop?)
  let renamed (fact : Expr) : MetaM Expr := do
    let motive ← withLocalDeclD `memory (mkConst ``Memory) fun x => mkLambdaFVars #[x] (read x)
    mkCongrArg motive fact
  if let .fvar name := memory then
    let some (_, stored, fact) := (← storeFacts).find? (·.1 == name) | return (here, none, none)
    let (final, proof?, stop?) ← next stored (← renamed fact) name
    -- A read that stops at this very store keeps the memory's name, which says which store it is.
    if stop?.isSome && final == read stored then return (here, none, stop?.map ({ · with read := here }))
    return (final, proof?, stop?)
  if memory.isAppOfArity ``Memory.storeBytes 4 then
    let #[earlier, base, length, bytes] := memory.getAppArgs | unreachable!
    let baseValue ← mkAppM ``BitVec.toNat #[base]
    let stored ← mkAppM ``HAdd.hAdd #[baseValue, length]
    let before ← if size?.isSome then mkAppM ``LE.le #[high, baseValue] else mkAppM ``LT.lt #[low, baseValue]
    match ← arith (mkOr before (← mkAppM ``LE.le #[stored, low])) with
    | .ok away =>
      let step ← match size?, fits? with
        | some size, some fits =>
          mkAppOptM ``Memory.readBytes_storeBytes_outside (#[earlier, bytes, base, address, length, size, away, fits].map some)
        | _, _ => mkAppOptM ``Memory.read_storeBytes_outside (#[earlier, base, length, bytes, address, away].map some)
      return ← next earlier step
    | .error why =>
      if let (some size, some fits) := (size?, fits?) then
        if let .ok start ← arith (← mkAppM ``LE.le #[baseValue, low]) then
          if let .ok finish ← arith (← mkAppM ``LE.le #[high, stored]) then
            let inside ← mkAppOptM ``Memory.readBytes_storeBytes_inside
              (#[earlier, bytes, base, address, length, size, start, finish, fits].map some)
            return (mkApp3 (mkConst ``readBytes) bytes address size, some inside, none)
      let instruction ← match name? with
        | some name => storedBy name
        | none => pure m!""
      return (here, none, some ⟨here, ← addMessageContext m!"stopped at the store of {length} bytes{instruction}, \
        to{indentExpr base}\nwhich it is not shown to miss or to lie inside.\n{why}"⟩)
  if let some state := memory.app1? ``MachineState.memory then
    for fact in ← stepFacts do
      let some (_, lhs, earlier) := (← instantiateMVars (← inferType fact)).eq? | continue
      if lhs == memory then return ← next earlier (← renamed fact)
    let mut why := none
    for (earlier, c, kept) in ← keptBy state do
      match ← misses c low high with
      | .ok away =>
        let step ← match size?, fits? with
          | some size, some fits => mkAppM ``MachineState.Except.readBytes #[kept, address, size, away, fits]
          | _, _ => pure <| mkApp6 (mkConst ``MachineState.Except.sameMemory) state earlier c kept address away
        return ← next (mkApp (mkConst ``MachineState.memory) earlier) step
      | .error reason => why := why <|> some reason
    if let some reason := why then
      return (here, none, some ⟨here, ← addMessageContext
        m!"stopped at the nested block that ended in {← describe state}: {reason}"⟩)
  return (here, none, none)

meta def walkRead (e : Expr) : MetaM (Expr × Option Expr × Option Stop) := do
  let_expr readBytes memory address size := e | return (e, none, none)
  let moves ← match memory with
    | .fvar name => pure <| (← storeFacts).any (·.1 == name)
    | _ => match memory.app1? ``MachineState.memory with
      | some state => pure <| (← later).any (state.containsFVar ·)
      | none => pure <| memory.isAppOfArity ``Memory.storeBytes 4
  unless moves do return (e, none, none)
  let bound ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[address], size], toExpr (2^64)]
  match ← arith bound with
  | .ok fits => walk memory address size fits
  | .error why => return (e, none, some ⟨e, m!"is not shown to end below 2^64.\n{why}"⟩)

meta def isByteRead (e : Expr) : MetaM Bool := do
  unless e.isApp do return false
  let memory := e.appFn!
  unless memory.isFVar || memory.isAppOfArity ``Memory.storeBytes 4 || memory.isAppOfArity ``MachineState.memory 1 do
    return false
  return (← inferType memory).isConstOf ``Memory

end ReadBack

open ReadBack in
simproc_decl readBack (readBytes _ _ _) := fun e => do
  let (final, proof?, _) ← walkRead e
  let some proof := proof? | return .continue
  return .visit { expr := final, proof? := some proof }

open ReadBack in
simproc_decl readBackByte (MachineState.memory _ _) := fun e => do
  let (final, proof?, _) ← walk e.appFn! e.appArg! none none
  let some proof := proof? | return .continue
  return .visit { expr := final, proof? := some proof }

namespace ReadBack

-- The read-back of the goal, or of hypotheses: registers, then memory.
meta def readBackTactic (locations : Array Term := #[]) : TacticM (TSyntax `tactic) := withMainContext do
  let mut names ← opened (← (← getMainGoal).getType)
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      for name in ← opened decl.type do
        unless names.contains name do names := names.push name
  let all ← lemmas names (← stepFacts) #[
    ← `(Lean.Parser.Tactic.simpLemma| rivet), ← `(Lean.Parser.Tactic.simpLemma| reduceCtorEq),
    ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte), ← `(Lean.Parser.Tactic.simpLemma| readBack),
    ← `(Lean.Parser.Tactic.simpLemma| ↓readBackByte), ← `(Lean.Parser.Tactic.simpLemma| readBytes_littleEndianAt),
    ← `(Lean.Parser.Tactic.simpLemma| BitVec.setWidth_eq), ← `(Lean.Parser.Tactic.simpLemma| BitVec.extractLsb'_eq_self),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceMul), ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceSub),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceAdd), ← `(Lean.Parser.Tactic.simpLemma| Nat.reducePow),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceLeDiff), ← `(Lean.Parser.Tactic.simpLemma| BitVec.reduceOfNat),
    ← `(Lean.Parser.Tactic.simpLemma| BitVec.sub_zero), ← `(Lean.Parser.Tactic.simpLemma| BitVec.add_zero),
    ← `(Lean.Parser.Tactic.simpLemma| MachineState.returnAddress),
    ← `(Lean.Parser.Tactic.simpLemma| ExecutionStatus.running.injEq)]
  if locations.isEmpty then `(tactic| simp only [$all,*]) else `(tactic| simp only [$all,*] at $[$locations]*)

-- Reads back, in place, the hypotheses that mention a later state, so they meet the goal's parts and
-- `rivet_arith` sees them as it sees the goal.
meta def known (goal : MVarId) : TacticM MVarId := goal.withContext do
  let later ← later
  let moved ← (← hypotheses).filterMapM fun decl => do
    if later.any ((← instantiateMVars decl.type).containsFVar ·) then some <$> Term.exprToSyntax decl.toExpr
    else pure none
  if moved.isEmpty then return goal
  setGoals [goal]
  evalTactic (← `(tactic| try $(← readBackTactic moved):tactic))
  let [goal] ← getGoals | throwError "rivet_close: the hypotheses contradict each other once read back"
  return goal

meta def facts (goal : MVarId) : MetaM (Array (Expr × Expr)) := goal.withContext do
  (← hypotheses).flatMapM fun decl => parts decl.toExpr decl.type

-- A goal's parts, each with what it is for when that is not what it says.
meta partial def leaves (goal : MVarId) : TacticM (Array (MVarId × Option MessageData)) := goal.withContext do
  let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations.headBeta
  if let some (left, right) := type.and? then
    let left ← mkFreshExprSyntheticOpaqueMVar left
    let right ← mkFreshExprSyntheticOpaqueMVar right
    goal.assign (← mkAppM ``And.intro #[left, right])
    return (← leaves left.mvarId!) ++ (← leaves right.mvarId!)
  if type.isForall then return ← leaves (← goal.intro1P).2
  if ← opens type then
    if isStructure (← getEnv) type.getAppFn.constName! then
      return ← (← goal.constructor).toArray.flatMapM leaves
    if let some unfolded ← unfoldDefinition? type then return ← leaves (← goal.replaceTargetDefEq unfolded.headBeta)
  -- `t.Except s c`: each register outside `c`, and each byte outside its ranges, is as it was.
  if let some (t, s, c) := type.app3? ``MachineState.Except then
    if t == s then
      goal.assign (← mkAppOptM ``MachineState.Except.refl #[s, c])
      return #[]
    let changed ← changedRegisters c
    let statement ← inferType (← mkAppOptM ``MachineState.Except.mk #[t, s, c])
    let .forallE _ registersType (.forallE _ memoryType _ _) _ := statement
      | throwError "rivet_close: unexpected statement{indentExpr statement}"
    let registersGoal ← mkFreshExprSyntheticOpaqueMVar registersType
    let (register, cases) ← registersGoal.mvarId!.intro `register
    let (_, cases) ← cases.intro `out
    let mut found := #[]
    for case in ← cases.cases register do
      let leaf ← case.mvarId.withContext do
        let some out := (← getLCtx).findFromUserName? `out | unreachable!
        let some name := case.ctorName | unreachable!
        if changed.contains name then
          let some inside := (← instantiateMVars out.type).not? | unreachable!
          case.mvarId.assign (← mkAbsurd (← case.mvarId.getType) (← mkDecideProof inside) out.toExpr)
          return none
        return some (← case.mvarId.clear out.fvarId, m!"`{mkConst name}` is not in the change{indentExpr c}\n\
          so it must end as it started. If it does change, list it.")
      if let some (leaf, note) := leaf then found := found.push (leaf, some note)
    let memoryGoal ← mkFreshExprSyntheticOpaqueMVar memoryType
    let (address, bytes) ← memoryGoal.mvarId!.intro `address
    let (away, bytes) ← bytes.intro `away
    let ranges ← changedRanges c
    let rangeType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
    let list ← mkListLit rangeType (ranges.map (·.1)).toList
    let mut bytes := bytes
    for (range, low, high) in ranges do
      let (type, proof) ← bytes.withContext do
        let value ← mkAppM ``BitVec.toNat #[.fvar address]
        let member ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Membership.mem #[list, range])
        discard <| Tactic.run member.mvarId! do
          evalTactic (← `(tactic| simp only [List.mem_cons, eq_self, true_or, or_true]))
        pure (mkOr (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[value, mkNatLit 1], low]) (← mkAppM ``LE.le #[high, value]),
          mkApp2 (.fvar away) range member)
      bytes := (← (← bytes.assert `away type proof).intro1P).2
    bytes ← bytes.clear away
    goal.assign (← mkAppOptM ``MachineState.Except.mk #[t, s, c, registersGoal, memoryGoal])
    return found.push (bytes, some m!"A byte `address` outside the change's memory{indentExpr c}\n\
      must end as it started. If a store or a nested block may change it, list its range.")
  return #[(← goal.replaceTargetDefEq type, none)]

-- Where each read of a part stopped short of the block's start.
meta def stops (type : Expr) : MetaM MessageData := do
  let reads ← IO.mkRef (#[] : Array Expr)
  forEachExpr type fun e => do
    if e.hasLooseBVars then return
    if e.isAppOfArity ``MachineState.registers 2 || e.isAppOfArity ``readBytes 3 || (← isByteRead e) ||
        ((e.isAppOfArity ``MachineState.status 1 || e.isAppOfArity ``MachineState.zeroFlag 1 ||
          e.isAppOfArity ``MachineState.carryFlag 1 || e.isAppOfArity ``MachineState.signFlag 1 ||
          e.isAppOfArity ``MachineState.overflowFlag 1) && e.appArg!.isFVar) then
      unless (← reads.get).contains e do reads.modify (·.push e)
  let mut why := m!""
  for read in ← reads.get do
    match_expr read with
    | MachineState.registers state register =>
      let name := (← whnfR register).constName?.getD .anonymous
      let inside ← (← keptBy state).filterM fun (_, c, _) => return (← changedRegisters c).contains name
      if let some (_, c, _) := inside[0]? then
        why := why ++ m!"\nThe read of `{register}` stopped at the nested block that ended in {← describe state}: \
          `{register}` is in its change{indentExpr c}\nand its postcondition does not say what it holds."
    | readBytes _ _ _ =>
      if let (_, _, some stop) ← walkRead read then
        why := why ++ m!"\nThe read{indentExpr stop.read}\n{stop.reason}"
    | _ =>
      if ← isByteRead read then
        if let (_, _, some stop) ← walk read.appFn! read.appArg! none none then
          why := why ++ m!"\nThe read{indentExpr stop.read}\n{stop.reason}"
      else if !(← keptBy read.appArg!).isEmpty then
        why := why ++ m!"\n`{read.getAppFn}` of {← describe read.appArg!} is the status or a flag after a \
          nested block. A change says nothing of them: only the block's postcondition does."
  return why

-- A part closes when it is a hypothesis or part of one, an instance of a general one, or has two
-- equal sides.
meta def finish (goal : MVarId) (facts : Array (Expr × Expr)) : TacticM Bool := goal.withContext do
  if ← goal.assumptionCore then return true
  let type ← instantiateMVars (← goal.getType)
  for (proof, part) in facts do
    if ← withReducible <| isDefEq part type then
      goal.assign proof
      return true
  let attempt (tactic : TSyntax `tactic) : TacticM Bool := do
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
  -- Not full `rfl`: it unfolds word arithmetic.
  if ← attempt (← `(tactic| with_reducible rfl)) then return true
  for (proof, part) in facts do
    if part.isForall then
      let proof ← Term.exprToSyntax (← mkExpectedTypeHint proof part)
      if ← attempt (← `(tactic| with_reducible apply $proof <;> with_reducible assumption)) then return true
  return false

meta partial def close (leaf : MVarId) (facts : Array (Expr × Expr)) : TacticM (Option MessageData) :=
    leaf.withContext do
  if ← finish leaf facts then return none
  let type ← instantiateMVars (← leaf.getType)
  if let some (left, right) := type.app2? ``Or then
    let saved ← saveState
    let leftGoal ← mkFreshExprSyntheticOpaqueMVar left
    match ← closeAll leftGoal.mvarId! with
    | none => leaf.assign (← mkAppOptM ``Or.inl #[left, right, leftGoal]); return none
    | some whyLeft =>
      saved.restore
      let rightGoal ← mkFreshExprSyntheticOpaqueMVar right
      match ← closeAll rightGoal.mvarId! with
      | none => leaf.assign (← mkAppOptM ``Or.inr #[left, right, rightGoal]); return none
      | some whyRight =>
        saved.restore
        return some m!" neither side holds.\nLeft:{whyLeft}\nRight:{whyRight}"
  -- Registers first: they need no arithmetic, and most parts need nothing else.
  let saved ← saveState
  setGoals [leaf]
  let quick ← try
      evalTactic (← registersBack type)
      match ← getGoals with
      | [] => pure true
      | [rest] => finish rest facts
      | _ => pure false
    catch _ => pure false
  if quick then return none
  saved.restore
  -- What a nested block's postcondition says a register or a read holds, where reading back stops.
  let mut values := #[]
  for (proof, part) in facts ++ (← hypotheses).map fun decl => (decl.toExpr, decl.type) do
    let some (_, lhs, _) := part.eq? | continue
    let state? := match lhs.app2? ``MachineState.registers with
      | some (state, _) => some state
      | none => (lhs.app3? ``readBytes).bind fun (memory, _, _) => memory.app1? ``MachineState.memory
    let some state := state? | continue
    unless (← keptBy state).isEmpty do values := values.push (← Term.exprToSyntax proof)
  setGoals [leaf]
  let read ← readBackTactic
  let step ← if values.isEmpty then pure read else
    `(tactic| first | (($read:tactic) <;> try simp only [$[$values:term],*]) | simp only [$[$values:term],*])
  try evalTactic step catch _ => setGoals [leaf]
  let [rest] ← getGoals | return none
  if ← finish rest facts then return none
  rest.withContext do
    let shown ← instantiateMVars (← rest.getType)
    let saved ← saveState
    try
      setGoals [rest]
      evalTactic (← `(tactic| rivet_arith))
      return none
    catch error =>
      saved.restore
      let reason ← stops shown
      unless (← reason.format).isEmpty do
        return some (← addMessageContext m!"{indentExpr shown}\nA read in it stopped short of the block's start.{reason}")
      addMessageContext m!"{indentExpr shown}\nis not a hypothesis and its sides are not the same.\n{error.toMessageData}"
where
  closeAll (goal : MVarId) : TacticM (Option MessageData) := do
    for (leaf, _) in ← leaves goal do
      if let some why ← close leaf facts then return some why
    return none

end ReadBack

open ReadBack in
@[tactic rivetClose] meta def evalRivetClose : Tactic := fun _ => withMainContext <| reporting m!"rivet_close" do
  let start ← getMainGoal
  let others := (← getGoals).tail
  let wanted := (← instantiateMVars (← start.getType)).headBeta
  let start ← start.replaceTargetDefEq wanted
  let mut failures := #[]
  unless ← start.assumptionCore do
    let known ← facts start
    for (leaf, note) in ← leaves start do
      let asked ← leaf.withContext do addMessageContext m!"{← instantiateMVars (← leaf.getType)}"
      let failure ← reporting m!"rivet_close: the part{indentD (note.getD asked)}\nwas not closed" do
        let saved ← saveState
        if (← close leaf known).isNone then return none
        -- The hypotheses are read back only for a part that needs them: most parts do not.
        saved.restore
        let moved ← ReadBack.known leaf
        return (← close moved (← facts moved)).map fun why => m!"{note.getD asked}\nRead back,{why}"
      if let some failure := failure then failures := failures.push failure
  unless failures.isEmpty do
    throwError "rivet_close: {failures.size} part(s) of{indentExpr wanted}\ndo not follow from what is known.\n\
      {MessageData.joinSep (failures.toList.map fun why => m!"• {why}") "\n"}"
  setGoals others

end Rivet
