module
public import Rivet.Laws.Block
public import Rivet.Tactics.Step
public import Rivet.Tactics.Arith
public meta import Lean
-- The read-back: every value of a later state, read back to the block's start. `rivet_known` closes a
-- goal that, read that way, is a hypothesis or has two equal sides. `rivet_arith` reads its goal and its
-- facts back the same way, then asks `lia`. The read-back itself asks no arithmetic: a read placed in a region passes a
-- store or a nested block by the names of the regions.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace ReadBack

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

-- The instruction that made a store's memory.
meta def storedBy (memory : Expr) : MetaM MessageData := do
  for decl in ← getLCtx do
    let_expr Step.StoredBy stored address operation := ← instantiateMVars decl.type | continue
    if stored == memory then
      let some address ← getNatValue? address | continue
      return m!" by `{operation}` at 0x{String.ofList (Nat.toDigits 16 address)}"
  return m!""

-- A store: the memory before it, where it wrote, how many bytes, and which; behind its name when it has one.
meta def store? (memory : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Option Expr)) := do
  let (stored, fact?) ← match memory with
    | .fvar name => match (← storeFacts).find? (·.1 == name) with
      | some (_, stored, fact) => pure (stored, some fact)
      | none => return none
    | _ => pure (memory, none)
  let_expr Memory.storeBytes earlier base length bytes := stored | return none
  return some (earlier, base, length, bytes, fact?)

-- The region `r` back through every store placed in a region apart from it and every nested block
-- whose change lists only regions apart from it: the earliest memory that is the same on `r`, a proof
-- `r.Same earliest memory`, and why it stopped short of a start (and whether that is a store into `r`
-- itself). Each step is a lookup: the region the store was placed in, and a hypothesis that
-- says the two are apart.
meta partial def regionBack (r memory : Expr) : MetaM (Expr × Option Expr × Option (MessageData × Bool)) := do
  let next (earlier step : Expr) : MetaM (Expr × Option Expr × Option (MessageData × Bool)) := do
    let (final, rest?, stop?) ← regionBack r earlier
    let proof ← match rest? with
      | some rest => mkAppM ``Region.Same.trans #[rest, step]
      | none => pure step
    return (final, some proof, stop?)
  let here (earlier : Expr) := mkAppOptM ``Region.Same.refl #[r, earlier]
  if let some (earlier, base, length, bytes, fact?) ← store? memory then
    let which := m!"the store of {length} bytes{← storedBy memory}, to{indentExpr base}\n"
    let some (other, placed) ← Places.placed? base length
      | return (memory, none, some (m!"stopped at {which}which no hypothesis places in a region.", false))
    if ← Places.same other r then return (memory, none, some (m!"stopped at {which}into `{r}` itself.", true))
    let some apart ← Places.apart? r other
      | return (memory, none, some (m!"stopped at {which}into `{other}`. Nothing says the two regions are apart: \
          state `{mkApp2 (mkConst ``Region.Apart) r other}`.", false))
    let step ← mkAppM ``Region.Same.store #[placed, apart, bytes, ← here earlier]
    return ← next earlier (← match fact? with
      | some fact => mkAppM ``Region.Same.of_eq #[fact, step]
      | none => pure step)
  if let some state := memory.app1? ``MachineState.memory then
    for fact in ← stepFacts do
      let some (_, lhs, earlier) := (← instantiateMVars (← inferType fact)).eq? | continue
      if lhs == memory then return ← next earlier (← mkAppM ``Region.Same.of_eq #[fact, ← here earlier])
    for (earlier, c, kept) in ← keptBy state do
      let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
      let low := mkApp (mkConst ``Region.base) r
      let high ← mkAppM ``HAdd.hAdd #[low, mkApp (mkConst ``Region.length) r]
      let motive ← withLocalDeclD `range pairType fun range => do
        mkLambdaFVars #[range] (mkOr (← mkAppM ``LE.le #[high, ← mkAppM ``Prod.fst #[range]])
          (← mkAppM ``LE.le #[← mkAppM ``Prod.snd #[range], low]))
      let mut proof ← mkAppOptM ``List.forall_mem_nil #[pairType, motive]
      let mut rest ← mkListLit pairType []
      for range in (← listItems (mkApp (mkConst ``Changes.memory) c)).reverse do
        let where_ := m!"stopped at the nested block that ended in {← describe state}: "
        let some other := (← instantiateMVars range).app1? ``Region.range
          | return (memory, none, some (m!"{where_}its change lists the range{indentExpr range}\nwhich is not a region.", false))
        if ← Places.same other r then
          return (memory, none, some (m!"{where_}`{r}` is in its change, so only its postcondition says what `{r}` \
            holds after it. State what you need there.", false))
        let some apart ← Places.apart? r other
          | return (memory, none, some (m!"{where_}its change lists `{other}`. Nothing says the two regions are \
              apart: state `{mkApp2 (mkConst ``Region.Apart) r other}`.", false))
        proof ← mkAppM ``Iff.mpr #[← mkAppOptM ``List.forall_mem_cons #[pairType, motive, range, rest],
          ← mkAppM ``And.intro #[← mkExpectedTypeHint apart (motive.beta #[range]), proof]]
        rest ← mkAppM ``List.cons #[range, rest]
      let misses ← mkExpectedTypeHint proof (← mkAppM ``Changes.Misses #[c, low, high])
      return ← next (mkApp (mkConst ``MachineState.memory) earlier)
        (← mkAppOptM ``MachineState.Except.same #[state, earlier, c, kept, r, misses])
  return (memory, none, none)

-- A placed read at a store it did not pass by its region. When the two pointers are a literal number of
-- bytes apart, what the laws ask is evaluated: the read misses the store, or is bytes of the value stored.
meta def atStore (read memory address size : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (earlier, base, length, bytes, fact?) ← store? memory | return none
  let some (distance, place) ← Places.between? address base | return none
  let (some bytesRead, some bytesStored) := (← getNatValue? size, ← getNatValue? length) | return none
  let some (_, placed) ← Places.placed? base length | return none
  let renamed (step : Expr) : MetaM Expr := do
    let some fact := fact? | return step
    let motive ← withLocalDeclD `memory (mkConst ``Memory) fun x =>
      mkLambdaFVars #[x] (mkApp3 (mkConst ``readBytes) x address size)
    mkEqTrans (← mkCongrArg motive fact) step
  let sum (a b : Expr) := mkAppM ``HAdd.hAdd #[a, b]
  let le (a b : Expr) := mkAppM ``LE.le #[a, b]
  if bytesStored ≤ distance && distance + bytesRead ≤ 2^64 then
    let after ← mkDecideProof (← le length (mkNatLit distance))
    let before ← mkDecideProof (← le (← sum (mkNatLit distance) size) (mkNatLit (2^64)))
    let outside ← mkAppM ``Region.Has.apart #[read, placed, place, after, before]
    let proof ← mkAppM ``Memory.readBytes_storeBytes_outside #[earlier, bytes, outside, ← mkAppM ``Region.Has.fits #[read]]
    return some (mkApp3 (mkConst ``readBytes) earlier address size, ← renamed proof)
  unless 0 < bytesRead && distance + bytesRead ≤ bytesStored do return none
  let_expr littleEndianAt _ value anchor := bytes | return none
  unless anchor == base do return none
  let within ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit distance, length])
  let inside ← mkDecideProof (← le (← sum (mkNatLit distance) size) length)
  let start ← mkAppM ``Region.Has.toNat_past #[placed, place, within]
  let proof ← mkAppM ``Region.Has.readBytes_stored #[placed, mkNatLit distance, start, inside, earlier, value]
  return some ((← inferType proof).eq?.get!.2.2, ← renamed proof)

-- Whether a memory is a later one: a store's, or a later state's.
meta def moves (memory : Expr) : MetaM Bool := do
  match memory with
  | .fvar name => return (← storeFacts).any (·.1 == name)
  | _ => match memory.app1? ``MachineState.memory with
    | some state => return (← later).any (state.containsFVar ·)
    | none => return memory.isAppOfArity ``Memory.storeBytes 4

-- One step of reading a read back: the region it is placed in, as far as that region is the same; then,
-- at the store it stopped at, what the literals between the two pointers say. A read no hypothesis
-- places stops there.
meta def readBack? (memory address size : Expr) : MetaM (Option (Expr × Expr)) := do
  unless ← moves memory do return none
  let some (r, placed) ← Places.placed? address size | return none
  if let (final, some same, _) ← regionBack r memory then
    return some (mkApp3 (mkConst ``readBytes) final address size, ← mkEqSymm (← mkAppM ``Region.Same.read #[same, placed]))
  atStore placed memory address size

-- `c.Same memory start`: every store between the two is placed in a region the change lists, and every
-- nested block's change is within it. Each step is a lookup in the change's list.
-- `c.Covers range`: the change lists the range, or covers the region it is a part of. Each step a lookup.
meta partial def covers (c : Expr) (range : Expr) : MetaM (Option Expr) := do
  let listed ← listItems (mkApp (mkConst ``Changes.memory) c)
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  if let some index ← listed.findIdxM? (Places.same · range) then
    let mut proof ← mkAppOptM ``List.Mem.head
      #[pairType, listed[index]!, ← mkListLit pairType (listed.toList.drop (index + 1))]
    for before in (listed.toList.take index).reverse do
      proof ← mkAppOptM ``List.Mem.tail #[pairType, none, before, none, proof]
    let member ← mkExpectedTypeHint proof (← mkAppM ``Membership.mem #[mkApp (mkConst ``Changes.memory) c, range])
    return some (← mkAppM ``Changes.Covers.listed #[member])
  let some r := (← instantiateMVars range).app1? ``Region.range | return none
  let some (root, offset, length, inside) ← Places.part? r | return none
  let some rest ← covers c (mkApp (mkConst ``Region.range) root) | return none
  return some (← mkAppM ``Changes.Covers.part #[rest, offset, length, inside])

meta partial def sameMemory (c memory start : Expr) : MetaM Expr := do
  if memory == start then return ← mkAppOptM ``Changes.Same.refl #[c, memory]
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  if let some (earlier, base, length, bytes, fact?) ← store? memory then
    let which := m!"the store of {length} bytes{← storedBy memory}, to{indentExpr base}\n"
    let some (r, placed) ← Places.placed? base length | throwError "{which}is not placed in a region."
    let some inside ← covers c (mkApp (mkConst ``Region.range) r)
      | throwError "{which}is into `{r}`, which the change{indentExpr c}\ndoes not list. If the block does write it, list it."
    let rest ← sameMemory c earlier start
    let proof ← mkAppOptM ``Changes.Same.store #[c, earlier, start, bytes, r, base, length, placed, inside, rest]
    let some fact := fact? | return proof
    return ← mkAppM ``Changes.Same.of_eq #[fact, proof]
  if let some state := memory.app1? ``MachineState.memory then
    for fact in ← stepFacts do
      let some (_, lhs, earlier) := (← instantiateMVars (← inferType fact)).eq? | continue
      if lhs == memory then return ← mkAppM ``Changes.Same.of_eq #[fact, ← sameMemory c earlier start]
    let nested ← keptBy state
    if let some ((earlier, inner, kept) : Expr × Expr × Expr) := nested[0]? then
      let motive ← withLocalDeclD `range pairType fun range => do
        mkLambdaFVars #[range] (← mkAppM ``Changes.Covers #[c, range])
      let mut proof ← mkAppOptM ``List.forall_mem_nil #[pairType, motive]
      let mut rest ← mkListLit pairType []
      for range in (← listItems (mkApp (mkConst ``Changes.memory) inner)).reverse do
        let some inside ← covers c range
          | throwError "the nested block that ended in {← describe state} may change{indentExpr range}\nwhich the \
              change{indentExpr c}\ndoes not list."
        proof ← mkAppM ``Iff.mpr #[← mkAppOptM ``List.forall_mem_cons #[pairType, motive, range, rest],
          ← mkAppM ``And.intro #[← mkExpectedTypeHint inside (motive.beta #[range]), proof]]
        rest ← mkAppM ``List.cons #[range, rest]
      let earlierMemory := mkApp (mkConst ``MachineState.memory) earlier
      return ← mkAppOptM ``Changes.Same.nested #[c, inner, state, earlier, start, kept, proof,
        ← sameMemory c earlierMemory start]
  throwError "the memory{indentExpr memory}\nis not traced back to the block's start."

end ReadBack

open ReadBack in
simproc_decl readBack (readBytes _ _ _) := fun e => do
  let_expr readBytes memory address size := e | return .continue
  if address.hasLooseBVars then return .continue
  let some (final, proof) ← readBack? memory address size | return .continue
  return .visit { expr := final, proof? := some proof }

namespace ReadBack

-- The read-back of the goal, or of hypotheses: registers, then memory.
meta def readBackTactic (locations : Array Term := #[]) (goal := false) : TacticM (TSyntax `tactic) := withMainContext do
  let mut names ← opened (← (← getMainGoal).getType)
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      for name in ← opened decl.type do
        unless names.contains name do names := names.push name
  let all ← lemmas names (← stepFacts) #[
    ← `(Lean.Parser.Tactic.simpLemma| rivet), ← `(Lean.Parser.Tactic.simpLemma| readBack)]
  if locations.isEmpty then `(tactic| simp only [$all,*])
  else if goal then `(tactic| simp only [$all,*] at $[$locations]* ⊢)
  else `(tactic| simp only [$all,*] at $[$locations]*)

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
  let [goal] ← getGoals | throwError "rivet_known: the hypotheses contradict each other once read back"
  return goal

meta def facts (goal : MVarId) : MetaM (Array (Expr × Expr)) := goal.withContext do
  (← hypotheses).flatMapM fun decl => parts decl.toExpr decl.type

-- A goal's parts, each with what it is for when that is not what it says.
meta partial def leaves (goal : MVarId) : TacticM (Array (MVarId × Option MessageData)) := goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  if type.isForall then return ← leaves (← goal.intro1P).2
  -- `t.Except s c`: each register outside `c` is as it was, and each store is into a region `c` lists.
  if let some (t, s, c) := type.app3? ``MachineState.Except then
    if t == s then
      goal.assign (← mkAppOptM ``MachineState.Except.refl #[s, c])
      return #[]
    let changed ← changedRegisters c
    let statement ← inferType (← mkAppOptM ``MachineState.Except.mk #[t, s, c])
    let .forallE _ registersType _ _ := statement
      | throwError "rivet_known: unexpected statement{indentExpr statement}"
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
    let memory ← try
        sameMemory c (mkApp (mkConst ``MachineState.memory) t) (mkApp (mkConst ``MachineState.memory) s)
      catch error =>
        throwError "the change{indentExpr c}\ndoes not cover what the block wrote: {error.toMessageData}"
    goal.assign (← mkAppOptM ``MachineState.Except.mk #[t, s, c, registersGoal, memory])
    return found
  -- A place is one part: a lookup first, and its two bounds only when that finds nothing.
  if type.isAppOf ``Region.Has then return #[(goal, none)]
  if type.getAppFn.constName?.any (isStructure (← getEnv)) then
    return ← (← goal.constructor).toArray.flatMapM leaves
  return #[(← goal.replaceTargetDefEq type, none)]

-- Where each read of a part stopped short of the block's start.
meta def stops (type : Expr) : MetaM MessageData := do
  let reads ← IO.mkRef (#[] : Array Expr)
  forEachExpr type fun e => do
    if e.hasLooseBVars then return
    if e.isAppOfArity ``MachineState.registers 2 || e.isAppOfArity ``readBytes 3 ||
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
    | readBytes memory address size =>
      if ← moves memory then
        match ← Places.placed? address size with
        | none =>
          why := why ++ m!"\nThe read{indentExpr read}\nis not placed, so it is not read back: no hypothesis `r.Has q n` \
            has its pointer. State it:{indentExpr (mkApp3 (mkConst ``Region.Has)
              (mkConst `r) address size)}\nfor the region `r` it lies in. {← Places.named}"
        | some (r, _) =>
          if let (final, _, some (reason, own)) ← regionBack r memory then
            why := why ++ m!"\nThe read{indentExpr read}\nplaced in `{r}`, {reason}"
            if let (true, some (_, base, length, _, _)) := (own, ← store? final) then
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
      if !(← keptBy read.appArg!).isEmpty then
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
    if sub.isAppOfArity ``MachineState.registers 2 || sub.isAppOfArity ``readBytes 3 then return true
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
meta def finish (goal : MVarId) (facts : Array (Expr × Expr)) : TacticM Bool := goal.withContext do
  if ← withReducible goal.assumptionCore then return true
  let type ← instantiateMVars (← goal.getType)
  -- A place, a permission of the image, and two regions apart: lookups.
  let found ← match_expr type with
    | Region.Has r pointer size => pure ((← Places.has? r pointer size).map (·.2))
    | Region.Apart r other => Places.apart? r other
    | Image.Reads image r => Places.grant? false image r
    | Image.Writes image r => Places.grant? true image r
    | _ => pure none
  if let some proof := found then
    goal.assign proof
    return true
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
  -- Not full `rfl`: it unfolds word arithmetic. `x ≤ x` has two equal sides too.
  if ← attempt (← `(tactic| with_reducible first | rfl | exact Nat.le_refl _ | exact BitVec.le_refl _)) then return true
  -- Literals alone, however spelled (`4106#64 = 4106`): evaluated.
  if !type.hasFVar && !type.hasMVar then
    if ← attempt (← `(tactic| decide)) then return true
  for (proof, part) in facts do
    if part.isForall then
      let proof ← Term.exprToSyntax (← mkExpectedTypeHint proof part)
      if ← attempt (← `(tactic| with_reducible apply $proof <;> with_reducible assumption)) then return true
  return false

meta partial def close (leaf : MVarId) (facts : Array (Expr × Expr)) : TacticM (Option MessageData) :=
    leaf.withContext do
  if ← finish leaf facts then return none
  -- `r.Same earlier later`: the region followed back from `later`.
  if let some (r, earlier, memory) := (← instantiateMVars (← leaf.getType)).app3? ``Region.Same then
    let (final, proof?, stop?) ← regionBack r memory
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
    `(tactic| ((try simp only [$[$values:term],*]); (try ($read:tactic)); (try simp only [$[$values:term],*])))
  try evalTactic step catch _ => setGoals [leaf]
  let [rest] ← getGoals | return none
  if ← finish rest facts then return none
  rest.withContext do
    let shown ← instantiateMVars (← rest.getType)
    if shown.isAppOf ``Region.Has then
      return some (← addMessageContext m!"{indentExpr shown}\nis not placed: no hypothesis `r.Has q n` has its pointer. \
        Prove the place, from one you have (`placed.first`, `placed.part`) or from its two bounds, and give it.")
    let reason ← stops shown
    unless (← reason.format).isEmpty do
      return some (← addMessageContext m!"{indentExpr shown}\nA read in it stopped short of the block's start.{reason}")
    if (← later).any (shown.containsFVar ·) then
      if let some name := shown.getAppFn.constName? then
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
      {← unfolded shown facts}\nRivet starts no arithmetic: prove it, `by rivet_arith` or `by rivet_arith only […]`, \
      and give it.{hint}")
where
  closeAll (goal : MVarId) : TacticM (Option MessageData) := do
    for (leaf, _) in ← leaves goal do
      if let some why ← close leaf facts then return some why
    return none

end ReadBack

namespace ReadBack

meta def closeTactic : TacticM Unit := withMainContext <| reporting m!"rivet_known" do
  let name := m!"rivet_known"
  let start ← getMainGoal
  let others := (← getGoals).tail
  let wanted := (← instantiateMVars (← start.getType)).headBeta
  let start ← start.replaceTargetDefEq wanted
  let mut failures := #[]
  unless ← withReducible start.assumptionCore do
    let known ← facts start
    for (leaf, note) in ← leaves start do
      let asked ← leaf.withContext do addMessageContext m!"{← instantiateMVars (← leaf.getType)}"
      let failure ← reporting m!"{name}: the part{indentD (note.getD asked)}\nwas not closed" do
        let saved ← saveState
        if (← close leaf known).isNone then return none
        -- The hypotheses are read back only for a part that needs them: most parts do not.
        saved.restore
        let moved ← ReadBack.known leaf
        return (← close moved (← facts moved)).map fun why => m!"{note.getD asked}\nRead back,{why}"
      if let some failure := failure then failures := failures.push failure
  unless failures.isEmpty do
    throwError "{name}: {failures.size} part(s) of{indentExpr wanted}\ndo not follow from what is known.\n\
      {MessageData.joinSep (failures.toList.map fun why => m!"• {why}") "\n"}"
  setGoals others

end ReadBack

@[tactic rivetKnown] meta def evalRivetKnown : Tactic := fun _ => ReadBack.closeTactic

meta partial def ReadBack.arith (stx : Syntax) : TacticM Unit := withMainContext do
  -- A record is proved field by field, as a listed record is given field by field. `lia` reads `∧` itself.
  let record ← do
    let type ← whnfR (← instantiateMVars (← getMainTarget))
    let env ← getEnv
    pure (type.getAppFn.constName?.any fun name => name != ``And && isStructure env name)
  if record then
    let others := (← getGoals).tail
    for field in ← (← getMainGoal).constructor do
      setGoals [field]
      arith stx
    setGoals others
    return
  let only := !stx[1].isNone
  let facts := if stx[2].isNone then #[] else stx[2][1].getSepArgs
  let others := (← getGoals).tail
  let mut goal ← getMainGoal
  let unlisted ← if only then goal.withContext do
      (← getLCtx).foldlM (init := #[]) fun unlisted decl => do
        if decl.isImplementationDetail then return unlisted
        return if ← isProp decl.type then unlisted.push decl.fvarId else unlisted
    else pure #[]
  let mut given := #[]
  for term in facts do
    let proof ← instantiateMVars (← Tactic.elabTerm term none)
    let type ← inferType proof
    -- `lia` does not instantiate a general statement, so one would be silently unused.
    if let .forallE _ domain _ _ ← whnfR type then
      unless ← isProp domain do
        throwError "rivet_arith: the fact `{term}` is general: `{type}`. `lia` uses only facts about \
          the goal's terms; give it its arguments."
    for (part, partType) in ← ReadBack.parts proof type do
      let (fact, next) ← (← goal.assert (← mkFreshUserName `fact) partType part).intro1P
      given := given.push fact
      goal := next
  -- Everything below works on a copy of the goal, and its proof is checked at once, as a lemma of its
  -- own, not at the end of your theorem.
  let outer := goal
  let outerType ← goal.withContext do instantiateMVars (← goal.getType)
  let copy ← goal.withContext do mkFreshExprSyntheticOpaqueMVar outerType
  let close : TacticM Unit := outer.withContext do
    outer.assign (← mkAuxTheorem outerType (← instantiateMVars copy))
  goal := copy.mvarId!
  -- The goal and the facts it may use, read back and in the `rivet` set's form, as every value Rivet
  -- writes is.
  setGoals [goal]
  let moved ← goal.withContext do
    let later ← ReadBack.later
    let used ← if only then given.mapM (·.getDecl) else ReadBack.hypotheses
    let moved ← used.filterM fun decl => return later.any ((← instantiateMVars decl.type).containsFVar ·)
    if moved.isEmpty && !later.any ((← instantiateMVars (← goal.getType)).containsFVar ·) then pure none else
      some <$> ReadBack.readBackTactic (← moved.mapM fun decl => Term.exprToSyntax decl.toExpr) (goal := true)
  if let some readBack := moved then
    evalTactic (← `(tactic| try $readBack:tactic))
  else
    let used ← goal.withContext do
      let used ← if only then given.mapM (·.getDecl) else ReadBack.hypotheses
      used.mapM fun decl => Term.exprToSyntax decl.toExpr
    evalTactic (← `(tactic| try simp only [rivet] at $[$used]* ⊢))
  let [read] ← getGoals | close; setGoals others; return
  goal := read
  -- `lia` never instantiates a general fact, but `grind` still prepares each one, within the budget.
  let hidden ← goal.withContext do
    (← getLCtx).foldlM (init := #[]) fun hidden decl => do
      if decl.isImplementationDetail then return hidden
      if unlisted.contains decl.fvarId then return hidden.push decl.fvarId
      let .forallE _ domain _ _ ← whnfR (← instantiateMVars decl.type) | return hidden
      return if (← isProp decl.type) && !(← isProp domain) then hidden.push decl.fvarId else hidden
  for fact in hidden.reverse do
    goal ← goal.tryClear fact
  setGoals [goal]
  let start ← IO.getNumHeartbeats
  let attempt := withTheReader Core.Context
    (fun context => { context with initHeartbeats := start, maxHeartbeats := arithBudget * 1000 })
    (evalTactic (← `(tactic| lia)))
  try
    tryCatchRuntimeEx (do attempt; close) fun error => do
      -- Its budget is its own; Lean's recursion limit is not, and stops the tactic.
      if error.isMaxRecDepth then throw error
      -- `grind` reports its own timeout as an ordinary failure, so compare the work done.
      if error.isMaxHeartbeat || (← IO.getNumHeartbeats) - start ≥ arithBudget * 1000 then
        throwError "rivet_arith: no proof within its budget of {arithBudget} heartbeats; \
          `maxHeartbeats` does not change it. Give it only the facts the goal needs: \
          `rivet_arith only [facts]`."
      throwError "rivet_arith: `lia` did not prove the goal from the facts in scope. Below is where it \
        stopped. Its assignment may or may not be a counterexample: `lia` drops what it does not read, \
        and may stop before it has tried everything.\n\
        - Facts the goal does not need, such as `%` or `/` facts and large `∨`s, can keep `lia` from a \
        proof: give it only those it needs, `rivet_arith only [facts]`.\n\
        - A term `lia` does not read, such as a mask, needs its meaning as an equation, e.g. \
        `x &&& 15#64 = x % 16#64`, proved through `toNat`.\n\
        - A goal that adds or subtracts a shifted value may need `grind`.\n\
        - `lia` does not unfold definitions: unfold them, or list facts about them.\
        {indentD (withoutRestatements error.toMessageData)}"
  finally
    IO.setNumHeartbeats start
  setGoals others

@[tactic rivetArith] meta def evalRivetArith : Tactic := ReadBack.arith

end Rivet
