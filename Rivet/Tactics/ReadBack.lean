module
public import Rivet.Laws.Block
public import Rivet.Tactics.Step
public meta import Lean
-- `rivet_known` closes a goal that, read back by the walk, is a hypothesis or has two equal sides.
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

namespace ReadBack

-- `Changes.Covers c r.range`: a region the change lists that `r` lies in.
meta def covers (c r : Expr) : MetaM (Option Expr) := do
  let listed ← listItems (mkApp (mkConst ``Changes.memory) c)
  let pairType ← rangeType
  for (item, index) in listed.zipIdx do
    let some region := (← instantiateMVars item).app1? ``Region.range | continue
    let some inside ← Places.inside? r region | continue
    let mut proof ← mkAppOptM ``List.Mem.head #[pairType, item, ← mkListLit pairType (listed.toList.drop (index + 1))]
    for before in (listed.toList.take index).reverse do
      proof ← mkAppOptM ``List.Mem.tail #[pairType, none, before, none, proof]
    let member ← mkExpectedTypeHint proof (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.memory) c, item])
    return some (← mkAppM ``Changes.Covers.inside #[member, inside])
  return none

-- `c.Same memory start`: every store between the two is placed in a region inside one the change lists,
-- and every region a nested block's change lists is.
meta partial def sameMemory (scope : Walk) (c memory start : Expr) : MetaM Expr := do
  let history := scope.history
  if memory == start then return ← mkAppOptM ``Changes.Same.refl #[c, memory]
  if let some (earlier, base, length, bytes, fact?) ← store? history memory then
    let which := describeStore history memory length base
    let places ← scope.placements base length
    let some (first, _) := places[0]? | throwError "{← which}is not placed in a region."
    let mut found := none
    for (r, placed) in places do
      if let some inside ← covers c r then found := some (r, placed, inside); break
    let some (r, placed, inside) := found
      | throwError "{← which}is into `{first}`, which the change{indentExpr c}\ndoes not list. If the block does write it, list it."
    let rest ← sameMemory scope c earlier start
    let proof ← mkAppOptM ``Changes.Same.store #[c, earlier, start, bytes, r, base, length, placed, inside, rest]
    let some fact := fact? | return proof
    return ← mkAppM ``Changes.Same.of_eq #[fact, proof]
  if let some state := memory.app1? ``MachineState.memory then
    if let some (earlier, fact) := history.equations[memory]? then
      return ← mkAppM ``Changes.Same.of_eq #[fact, ← sameMemory scope c earlier start]
    let motive ← withLocalDeclD `range (← rangeType) fun range => do
      mkLambdaFVars #[range] (← mkAppM ``Changes.Covers #[c, range])
    let mut missing := none
    for (earlier, inner, kept) in history.keptBy state do
      match ← allRanges inner motive fun range => do
          let some r := (← instantiateMVars range).app1? ``Region.range | return none
          covers c r with
      | .inl proof =>
        return ← mkAppOptM ``Changes.Same.nested #[c, inner, state, earlier, start, kept, proof,
          ← sameMemory scope c (mkApp (mkConst ``MachineState.memory) earlier) start]
      | .inr range => missing := missing <|> some range
    if let some range := missing then
      throwError "the nested block that ended in {← describe state} may change{indentExpr range}\nwhich no region \
        the change{indentExpr c}\nlists holds."
  throwError "the memory{indentExpr memory}\nis not traced back to the block's start."

-- `c.SameXmm state s`, with no vector register looked at: no step from `s` to `state` wrote one, and each
-- nested block's change lists only vector registers `c` lists.
meta partial def sameXmm (history : History) (c state s : Expr) : MetaM (Option Expr) := do
  if state == s then return some (← mkAppOptM ``Changes.SameXmm.refl #[c, s])
  if let some (file, equation) := history.equations[mkApp (mkConst ``MachineState.xmmRegisters) state]? then
    let some earlier := file.app1? ``MachineState.xmmRegisters | return none
    let some rest ← sameXmm history c earlier s | return none
    return some (← mkAppM ``Changes.SameXmm.of_eq #[equation, rest])
  let listed ← changedRegisters c ``Changes.xmm
  for (earlier, inner, kept) in history.keptBy state do
    unless (← changedRegisters inner ``Changes.xmm).all listed.contains do continue
    let some rest ← sameXmm history c earlier s | continue
    let within ← withLocalDeclD `register (mkConst ``Xmm) fun register => do
      mkForallFVars #[register] (← mkArrow
        (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.xmm) inner, register])
        (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.xmm) c, register]))
    return some (← mkAppM ``Changes.SameXmm.nested #[kept, ← mkDecideProof within, rest])
  return none

-- `∀ register, register ∉ c.… → …`, the statement of `Except` for a register file: a case for each
-- register, closed if the change lists it and a part to prove if not.
meta def unlisted (c : Expr) (listed : Name) (statement : Expr) : MetaM (Expr × Array (MVarId × Option MessageData)) := do
  let changed ← changedRegisters c listed
  let goal ← mkFreshExprSyntheticOpaqueMVar statement
  let (register, cases) ← goal.mvarId!.intro `register
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
  return (goal, found)

-- A goal's parts, each with what it is for when that is not what it says.
meta partial def leaves (scope : Walk) (goal : MVarId) : TacticM (Array (MVarId × Option MessageData)) :=
    goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  if type.isForall then return ← leaves scope (← goal.intro1P).2
  -- `t.Except s c`: each register and vector register outside `c` is as it was, each store is into a
  -- region `c` lists, and the kernel is as it was unless `c` lists it.
  if let some (t, s, c) := type.app3? ``MachineState.Except then
    if t == s then
      goal.assign (← mkAppOptM ``MachineState.Except.refl #[s, c])
      return #[]
    let statement ← inferType (← mkAppOptM ``MachineState.Except.mk #[t, s, c])
    let .forallE _ registersType (.forallE _ xmmType _ _) _ := statement
      | throwError "rivet_known: unexpected statement{indentExpr statement}"
    let (registers, found) ← unlisted c ``Changes.registers registersType
    let (xmm, found) ← match ← sameXmm scope.history c t s with
      | some same => pure (same, found)
      | none => do
        let (xmm, parts) ← unlisted c ``Changes.xmm xmmType
        pure (xmm, found ++ parts)
    let memory ← try
        sameMemory scope c (mkApp (mkConst ``MachineState.memory) t) (mkApp (mkConst ``MachineState.memory) s)
      catch error =>
        throwError "the change{indentExpr c}\ndoes not cover what the block wrote: {error.toMessageData}"
    let listed := mkApp (mkConst ``Changes.kernel) c
    let out ← mkEq listed (mkConst ``Bool.false)
    let same ← mkEq (mkApp (mkConst ``MachineState.kernel) t) (mkApp (mkConst ``MachineState.kernel) s)
    let (kernel, found) ← if (← whnfD listed).isConstOf ``Bool.true then
        pure (← withLocalDeclD `out out fun h => do
          mkLambdaFVars #[h] (← mkAbsurd same h (← mkDecideProof (mkNot out))), found)
      else do
        let kept ← mkFreshExprSyntheticOpaqueMVar same
        pure (mkLambda `out .default out kept, found.push (kept.mvarId!, some m!"the kernel is not in the \
          change{indentExpr c}\nso it must end as it started. If it does change, list it: `kernel := true`."))
    goal.assign (← mkAppOptM ``MachineState.Except.mk #[t, s, c, registers, xmm, memory, kernel])
    return found
  -- A place is one part: a lookup first, and its two bounds only when that finds nothing.
  if !type.isAppOf ``Region.Has && (← splits type) then
    return ← (← goal.constructor).toArray.flatMapM (leaves scope)
  return #[(← goal.replaceTargetDefEq type, none)]

-- Where each read of a part stopped short of the block's start.
meta def stops (scope : Walk) (type : Expr) : MetaM MessageData := do
  let history := scope.history
  let reads ← IO.mkRef (#[] : Array Expr)
  forEachExpr type fun e => do
    if e.hasLooseBVars then return
    if (location? e).isSome then
      unless (← reads.get).contains e do reads.modify (·.push e)
  let mut why := m!""
  for read in ← reads.get do
    if let some (listed, _) := registerFile? read then
      let state := read.appFn!.appArg!
      let register := read.appArg!
      let name := (← whnfR register).constName?.getD .anonymous
      let inside ← (history.keptBy state).filterM fun (_, c, _) => return (← changedRegisters c listed).contains name
      if let some (_, c, _) := inside[0]? then
        why := why ++ m!"\nThe read of `{register}` stopped at the nested block that ended in {← describe state}: \
          `{register}` is in its change{indentExpr c}\nand its postcondition does not say what it holds."
      continue
    if let some state := read.app1? ``MachineState.kernel then
      unless (history.keptBy state).isEmpty do
        why := why ++ m!"\nThe kernel was read back to the nested block that ended in {← describe state}: its change \
          lists the kernel, and its postcondition does not say what the kernel is."
      continue
    match_expr read with
    | readBytes memory address size =>
      if moves history memory then
        match (← scope.placements address size)[0]? with
        | none =>
          why := why ++ m!"\nThe read{indentExpr read}\nis not placed, so it is not read back: no hypothesis `r.Has q n` \
            has its pointer. State it:{indentExpr (mkApp3 (mkConst ``Region.Has)
              (mkConst `r) address size)}\nfor the region `r` it lies in; `r.Has p r.length` places every part of `r`. \
              {← Places.named (← scope.places)}"
        | some (r, _) =>
          if let (final, _, some whyStopped) ← scope.regionStep r memory then
            let (reason, own) ← whyStopped
            why := why ++ m!"\nThe read{indentExpr read}\nplaced in `{r}`, {reason}"
            if let (true, some (_, base, length, _, _)) := (own, ← store? history final) then
              if (← Places.between? address base).isSome then
                why := why ++ m!"\nThe store holds only some of the read's bytes. Rivet reads back a read wholly outside \
                  a store or wholly inside it: read the bytes as two such reads."
                continue
              let number (e : Expr) := mkAppM ``BitVec.toNat #[e]
              let ends (e n : Expr) := do mkAppM ``HAdd.hAdd #[← number e, n]
              let misses := mkOr (← mkAppM ``LE.le #[← ends address size, ← number base])
                (← mkAppM ``LE.le #[← ends base length, ← number address])
              why := why ++ m!"\nRivet compares two pointers into one region only when they are a literal number of bytes apart. \
                Place the two in regions that are apart, or prove how they lie and rewrite the read with the law:{indentExpr misses}\n\
                for `Memory.readBytes_storeBytes_outside`, or\
                {indentD m!"{← number address} = {← number base} + offset"}\n\
                for `Region.Has.readBytes_stored`."
    | _ =>
      if !(history.keptBy read.appArg!).isEmpty then
        why := why ++ m!"\n`{read.getAppFn}` of {← describe read.appArg!} is the status or a flag after a \
          nested block. A change says nothing of them: only the block's postcondition does."
  return why

-- For an error only: what a statement is about: its variables, and the registers, reads and fields it
-- reads.
meta def atomsOf (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let isAtom (sub : Expr) : MetaM Bool := do
    if sub.isFVar then
      return !((← inferType sub).getAppFn.constName?.any (isStructure env)) && !(← isProof sub)
    if (registerFile? sub).isSome || sub.isAppOfArity ``readBytes 3 then return true
    let some name := sub.getAppFn.constName? | return false
    unless sub.getAppNumArgs == 1 && sub.appArg!.isFVar do return false
    unless (← getProjectionFnInfo? name).isSome do return false
    return !(← inferType sub.appArg!).isConstOf ``MachineState
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun sub => do
    if sub.hasLooseBVars then return
    if (← isAtom sub) && !(← found.get).contains sub then found.modify (·.push sub)
  found.get

-- For an error only: where two statements first differ.
meta partial def differ (a b : Expr) : MetaM (Expr × Expr) := do
  if a.isApp && b.isApp && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs then
    let pairs ← (a.getAppArgs.zip b.getAppArgs).filterM fun (x, y) => return !(← withReducible <| isDefEq x y)
    if let #[(x, y)] := pairs then return ← differ x y
  return (a, b)

-- For an error only: a hypothesis that says `type` once definitions are unfolded. Never used to close.
meta def unfolded (type : Expr) (facts : Array (Expr × Expr)) : MetaM MessageData := do
  for (proof, part) in facts do
    unless part.getAppFn == type.getAppFn do continue
    let start ← IO.getNumHeartbeats
    let same ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun context => { context with initHeartbeats := start, maxHeartbeats := 200 * 1000 })
        (withNewMCtxDepth <| isDefEq part type))
      (fun _ => pure false)
    if same then
      let (theirs, ours) ← differ part type
      return m!"\nThe hypothesis{indentD m!"{proof} : {part}"}\nsays this with{indentExpr theirs}\nfor{indentExpr ours}\n\
        which are the same only by unfolding a definition. Rivet compares statements as written, through \
        `abbrev`s only: state both one way."
  return m!""

-- A part closes when it is a hypothesis or part of one, an instance of a general one, or has two
-- equal sides.
meta def finish (w : Walk) (goal : MVarId) (facts : Array (Expr × Expr)) : TacticM Bool :=
    goal.withContext do
  if ← withReducible goal.assumptionCore then return true
  let type ← instantiateMVars (← goal.getType)
  -- A place, a permission of the kernel, and two regions apart: lookups.
  let found ← match_expr type with
    | Region.Has r pointer size => Places.has? (← w.places) r pointer size
    | Region.Apart r other => Places.apart? (← w.places) r other
    | Kernel.Reads kernel r => Places.grant? (← w.places) false kernel r
    | Kernel.Writes kernel r => Places.grant? (← w.places) true kernel r
    | _ => pure none
  if let some proof := found then
    goal.assign proof
    return true
  for (proof, part) in facts do
    if ← withReducible <| isDefEq part type then
      goal.assign proof
      return true
  -- Not full `rfl`: it unfolds word arithmetic. `x ≤ x` has two equal sides too.
  if ← Step.closes (← `(tactic| with_reducible first | rfl | exact Nat.le_refl _ | exact BitVec.le_refl _)) goal then
    return true
  -- Literals alone, however spelled (`4106#64 = 4106`): evaluated.
  if !type.hasFVar && !type.hasMVar then
    if ← Step.closes (← `(tactic| decide)) goal then return true
  for (proof, part) in facts do
    if part.isForall then
      let proof ← Term.exprToSyntax (← mkExpectedTypeHint proof part)
      if ← Step.closes (← `(tactic| with_reducible apply $proof <;> with_reducible assumption)) goal then return true
  return false

-- A status asked for at one address, where the steps say the block is at another.
meta def elsewhere (type : Expr) : MetaM (Option MessageData) := do
  let some (_, status, asked) := type.eq? | return none
  let some state := status.app1? ``MachineState.status | return none
  let some asked := asked.app1? ``ExecutionStatus.running | return none
  let some asked ← Fetch.addressValue? asked | return none
  let some (_, at_, _) ← Step.findPc? state | return none
  if at_ == asked then return none
  return some m!" the block is at 0x{Fetch.hex at_}, and this asks for 0x{Fetch.hex asked}. Step to it, \
    `rivet_step to 0x{Fetch.hex asked}`, or ask for where the block is."

meta partial def close (scope : Walk) (leaf : MVarId) (facts : Array (Expr × Expr)) : TacticM (Option MessageData) :=
    leaf.withContext do
  let type ← instantiateMVars (← leaf.getType)
  if type.isAppOfArity ``Eq 3 then
    let result ← scope.walk type
    if result.expr.isConstOf ``True then
      leaf.assign (← mkEqMPR (← result.getProof' type) (mkConst ``True.intro))
      return none
  if ← finish scope leaf facts then return none
  -- `r.Same earlier later`: the region followed back from `later`.
  if let some (r, earlier, memory) := (← instantiateMVars (← leaf.getType)).app3? ``Region.Same then
    let mut final := memory
    let mut proof? := none
    let mut stop? := none
    while final != earlier do
      let mut next := final
      let mut step? := none
      for (proof, part) in facts do
        let some (other, from_, to_) := part.app3? ``Region.Same | continue
        if from_ == earlier && to_ == final && (← Places.same other r) then
          next := earlier
          step? := some proof
          break
      if step?.isNone then
        let (prev, step, why) ← scope.regionStep r final
        next := prev
        step? := step
        stop? ← liftMetaM (why.mapM id)
      let some step := step? | break
      proof? ← match proof? with
        | some after => some <$> mkAppM ``Region.Same.trans #[step, after]
        | none => pure (some step)
      final := next
    if final == earlier then
      leaf.assign (← match proof? with
        | some proof => pure proof
        | none => mkAppOptM ``Region.Same.refl #[r, earlier])
      return none
    return some (← addMessageContext m!"{indentExpr (← leaf.getType)}\nFollowing `{r}` back from{indentExpr memory}\n\
      {match stop? with
        | some (reason, true) => m!"{reason} So `{r}` is not the same across it. Say instead what the store left alone: \
            a read that misses it, by `Memory.readBytes_storeBytes_outside`."
        | some (reason, false) => reason
        | none => m!"ended at{indentExpr final}\nwhich is not the memory asked for."}")
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
  let some rest ← scope.readBack leaf | return none
  if ← finish scope rest facts then return none
  if let some why ← elsewhere type then return some why
  rest.withContext do
    let shown ← instantiateMVars (← rest.getType)
    for (source, part) in facts do
      unless part.getAppFn == shown.getAppFn || part.isForall do continue
      let result ← scope.walk part
      unless ← Places.same result.expr shown do continue
      rest.assign (← match result.proof? with
        | some equal => mkEqMP equal source
        | none => mkExpectedTypeHint source shown)
      return none
    let notes ← scope.notes type shown
    if shown.isAppOf ``Region.Has then
      let parent ← match ← Places.part? shown.appFn!.appFn!.appArg! with
        | some (root, _, _, _) => pure m!" Or place what it is part of: `{root}.Has p {root}.length` places each part of `{root}`."
        | none => pure m!""
      return some (← addMessageContext m!"{indentExpr shown}\nis not placed: no hypothesis `r.Has q n` has its pointer. \
        Prove the place, from one you have (`placed.part`) or from its two bounds, and give it.{parent}{notes}")
    let reason ← stops scope shown
    unless (← reason.format).isEmpty do
      return some (← addMessageContext m!"{indentExpr shown}\nA read in it stopped short of the block's start.{reason}{notes}")
    if shown.hasAnyFVar scope.history.later.contains then
      let env ← getEnv
      if let some name := shown.getAppFn.constName?.filter fun name => (env.find? name).any (·.isDefinition) then
        let earlier := (← facts.findM? fun (_, part) => return part.getAppFn == shown.getAppFn).map (·.1)
        let given := match earlier with
          | some proof => m!"`{proof}.carry (by rivet_known)`"
          | none => m!"`{mkConst (name ++ `carry)} (by rivet_known)` with the fact for the earlier memory"
        let lemma := if (← getEnv).contains (name ++ `carry) then m!"" else
          m!" Prove once that it carries: `theorem {mkConst name}.carry (same : r.Same m m') (h : {mkConst name} m …) : \
            {mkConst name} m' …`, for the region `r` its reads lie in."
        return some (← addMessageContext m!"{indentExpr shown}\nis about a later memory, and `{mkConst name}` is a \
          `def`: Rivet does not see its reads.{lemma} Then give {given}.")
      return some (← addMessageContext m!"{indentExpr shown}\nis about a later memory, and is not a read Rivet \
        can place. State it as reads, or carry it from the earlier memory by a lemma from `r.Same m m'`.")
    let atoms ← atomsOf shown
    let related := facts.filter fun (_, part) => atoms.any fun atom => (part.find? (· == atom)).isSome
    let hint := if related.isEmpty then m!"" else
      m!"\nFacts in scope about its variables: {MessageData.joinSep (related.toList.map fun (proof, _) => m!"`{proof}`") ", "}."
    return some (← addMessageContext m!"{indentExpr shown}\nis not a hypothesis and its sides are not the same.\
      {← unfolded shown facts}\nRivet starts no arithmetic: prove it, `by rivet_arith [facts]`, \
      and give it.{hint}{notes}")
where
  closeAll (goal : MVarId) : TacticM (Option MessageData) := do
    for (leaf, _) in ← leaves scope goal do
      if let some why ← close scope leaf facts then return some why
    return none

meta def proveKnown (start : MVarId) (index : TacticM Walk) : TacticM Unit := start.withContext do
  let wanted := (← instantiateMVars (← start.getType)).headBeta
  let start ← start.replaceTargetDefEq wanted
  let mut failures := #[]
  unless ← withReducible start.assumptionCore do
    let scope ← index
    let facts ← scope.parts
    for (leaf, note) in ← leaves scope start do
      let asked ← leaf.withContext do addMessageContext m!"{← instantiateMVars (← leaf.getType)}"
      let failure ← reporting m!"rivet_known: the part{indentD (note.getD asked)}\nwas not closed" do
        return (← close scope leaf facts).map fun why => m!"{note.getD asked}\nRead back,{why}"
      if let some failure := failure then failures := failures.push failure
  unless failures.isEmpty do
    throwError "rivet_known: {failures.size} part(s) of{indentExpr wanted}\ndo not follow from what is known.\n\
      {MessageData.joinSep (failures.toList.map fun why => m!"• {why}") "\n"}"


@[tactic rivetKnown] meta def evalRivetKnown : Tactic := fun _ => withMainContext <| reporting m!"rivet_known" do
  let start ← getMainGoal
  let others := (← getGoals).tail
  proveKnown start (Walk.make start)
  setGoals others

end ReadBack

end Rivet.Internal
