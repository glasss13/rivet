module
public import Rivet.Tactics.Fetch
public import Rivet.Tactics.Places
public meta import Rivet.Tactics.Registers
public meta import Lean
-- The walk: what a location of a later state holds. It goes back past each step, store and nested block
-- that could not have touched the location, to the one that could, which says what it holds, or to where
-- it stops: the block's start, or a nested block's end for what that block changed. There a fact says what
-- the location holds: an equation in scope `location = value`, as written. Every tactic reads back by it.
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

namespace Step

-- Where a state is: a hypothesis `state.status = .running address`, or a record's field that says so.
-- The address as written, its value, and the proof.
meta def findPc? (state : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  let stepped ← ReadBack.isStepState state
  if let some proof := (← getLCtx).findDeclRev? fun decl =>
      if stepped && decl.type.eq?.any (fun (_, lhs, _) =>
        lhs.isAppOfArity ``MachineState.status 1 && lhs.appArg! == state) then some decl else none then
    let some (_, _, rhs) := proof.type.eq? | return none
    if let some address := rhs.app1? ``ExecutionStatus.running then
      if let some pc ← Fetch.addressValue? address then return (address, pc, proof.toExpr)
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

end Step

namespace ReadBack

-- A state by its name, or by where it is when no step named it.
meta def describe (state : Expr) : MetaM MessageData := do
  if let some id := state.fvarId? then
    unless ((← getLCtx).get! id).userName.hasMacroScopes do return m!"`{state}`"
  if let some (_, pc, _) ← Step.findPc? state then return m!"the state at 0x{Fetch.hex pc}"
  return m!"an unnamed state"

-- A store, for errors: its size, the instruction that made it, and where it wrote.
meta def describeStore (history : History) (memory length base : Expr) : MetaM MessageData := do
  let mut by_ := m!""
  if let some (address, operation) := history.instructions[memory]? then
    if let some pc ← getNatValue? address then by_ := m!" by `{operation}` at 0x{Fetch.hex pc}"
  return m!"the store of {length} bytes{by_}, to{indentExpr base}\n"

-- A store: the memory before it, where it wrote, how many bytes, and which; behind its name when it has one.
meta def store? (history : History) (memory : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Option Expr)) := do
  let (stored, fact?) ← match memory with
    | .fvar name => match history.stores[name]? with
      | some (stored, fact) => pure (stored, some fact)
      | none => return none
    | _ => pure (memory, none)
  let_expr Memory.storeBytes earlier base length bytes := stored | return none
  return some (earlier, base, length, bytes, fact?)

-- What to state for a store or a nested block into `other` that `r` is not known to be apart from.
meta def notApart (r other : Expr) : MetaM MessageData := do
  if (← Places.inside? other r).isSome then
    return m!"`{other}` lies in `{r}`, so the two are never apart. Place the read in a part of `{r}` apart from it."
  return m!"Nothing says the two regions are apart: state `{mkApp2 (mkConst ``Region.Apart) r other}`."

meta structure Walk where
  history : History
  context : Simp.Context
  reductions : Simp.SimprocsArray
  candidates : Std.HashMap Expr (Array (Nat × Expr × Expr × Expr))
  count : Nat
  fields : Array (Expr × Expr)
  readPlaces : IO.Ref (Std.HashMap (Expr × Expr) (Array (Expr × Expr)))
  regions : IO.Ref (Std.HashMap (Expr × Expr) (Expr × Option Expr))
  apartness : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr))
  placeCache : IO.Ref (Option (Array (Expr × Expr)))
  answers : IO.Ref (Std.HashMap (Nat × Expr) Simp.Result)
  used : IO.Ref (Array (Expr × Expr × Expr))
  skipped : IO.Ref (Array (Expr × Expr × MessageData))

private meta def bucket (lhs : Expr) := if lhs.isAppOfArity ``readBytes 3 then lhs.getArg! 0 else lhs

meta def rangeType : MetaM Expr := mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]

-- `∀ range ∈ c.memory, motive range`, from a proof for each range; or the first range without one.
meta def allRanges (c motive : Expr) (each : Expr → MetaM (Option Expr)) : MetaM (Expr ⊕ Expr) := do
  let pairType ← rangeType
  let mut proof ← mkAppOptM ``List.forall_mem_nil #[pairType, motive]
  let mut rest ← mkListLit pairType []
  for range in (← listItems (mkApp (mkConst ``Changes.memory) c)).reverse do
    let some holds ← each range | return .inr range
    proof ← mkAppM ``Iff.mpr #[← mkAppOptM ``List.forall_mem_cons #[pairType, motive, range, rest],
      ← mkAppM ``And.intro #[← mkExpectedTypeHint holds (motive.beta #[range]), proof]]
    rest ← mkAppM ``List.cons #[range, rest]
  return .inl proof

-- Whether a memory is a later one: a store's, or a later state's.
meta def moves (history : History) (memory : Expr) : Bool :=
  match memory with
  | .fvar name => history.stores.contains name
  | _ => match memory.app1? ``MachineState.memory with
    | some state => state.hasAnyFVar history.later.contains
    | none => memory.isAppOfArity ``Memory.storeBytes 4

-- What a location is of: the state of a register or a vector register, its low bits as an instruction
-- reads them, its status, a flag or its kernel; or the memory of a read.
meta def location? (e : Expr) : Option Expr :=
  let register (e : Expr) := (registerFile? e).isSome && (e.getArg! 1).isConst
  if register e then some (e.getArg! 0)
  else if e.isAppOfArity ``BitVec.setWidth 3 && register (e.getArg! 2) then some ((e.getArg! 2).getArg! 0)
  else if e.isAppOfArity ``readBytes 3 then some (e.getArg! 0)
  else if [``MachineState.status, ``MachineState.zeroFlag, ``MachineState.carryFlag, ``MachineState.signFlag,
      ``MachineState.overflowFlag, ``MachineState.kernel].any (e.isAppOfArity · 1) then some e.appArg!
  else none

private meta def Walk.select (w : Walk) (e : Expr) : MetaM (Option Simp.Result) := do
  let register := e.appArg!
  unless register.isConst do return none
  let some (rhs, proof) := w.history.equations[e.appFn!]? | return none
  let mut value := rhs.beta #[register]
  repeat
    let_expr ite _ test _ yes no := value | break
    let_expr Eq _ left right := test | break
    unless left.isConst && right.isConst do break
    value := if left == right then yes else no
  return some { expr := value, proof? := some (← mkCongrFun proof register) }

mutual
meta partial def Walk.apart (w : Walk) (a b : Expr) : MetaM (Option Expr) := do
  let key := (a, b)
  if let some result := (← w.apartness.get)[key]? then return result
  let result ← Places.apart? (← w.places) a b
  w.apartness.modify (·.insert key result)
  return result

meta partial def Walk.placements (w : Walk) (p n : Expr) := do
  let key := (p, n)
  if let some hit := (← w.readPlaces.get)[key]? then return hit
  let found ← Places.places (← w.places) p n
  w.readPlaces.modify (·.insert key found)
  return found

-- One memory transition, with its equality on the region or a delayed explanation of the stop.
meta partial def Walk.regionStep (w : Walk) (r memory : Expr) :
    MetaM (Expr × Option Expr × Option (MetaM (MessageData × Bool))) := do
  let next (earlier step : Expr) : MetaM (Expr × Option Expr × Option (MetaM (MessageData × Bool))) :=
    pure (earlier, some step, none)
  let here (earlier : Expr) := mkAppOptM ``Region.Same.refl #[r, earlier]
  if let some (earlier, base, length, bytes, fact?) ← store? w.history memory then
    let which := describeStore w.history memory length base
    let places ← w.placements base length
    if places.isEmpty then
      return (memory, none, some (do return (m!"stopped at {← which}which no hypothesis places in a region.", false)))
    for (other, placed) in places do
      if let some apart ← w.apart r other then
        let step ← mkAppM ``Region.Same.store #[placed, apart, bytes, ← here earlier]
        return ← next earlier (← match fact? with
          | some fact => mkAppM ``Region.Same.of_eq #[fact, step]
          | none => pure step)
    let other := places[0]!.1
    return (memory, none, some (do
      if (← Places.inside? other r).isSome || (← Places.inside? r other).isSome then
        return (m!"stopped at {← which}into `{other}`, which `{r}` meets.", true)
      return (m!"stopped at {← which}into `{other}`. {← notApart r other}", false)))
  if let some state := memory.app1? ``MachineState.memory then
    if let some (earlier, fact) := w.history.equations[memory]? then
      return ← next earlier (← mkAppM ``Region.Same.of_eq #[fact, ← here earlier])
    let low := mkApp (mkConst ``Region.base) r
    let high ← mkAppM ``HAdd.hAdd #[low, mkApp (mkConst ``Region.length) r]
    let motive ← withLocalDeclD `range (← rangeType) fun range => do
      mkLambdaFVars #[range] (mkOr (← mkAppM ``LE.le #[high, ← mkAppM ``Prod.fst #[range]])
        (← mkAppM ``LE.le #[← mkAppM ``Prod.snd #[range], low]))
    let mut stop := none
    for (earlier, c, kept) in w.history.keptBy state do
      match ← allRanges c motive fun range => do
          let some other := (← instantiateMVars range).app1? ``Region.range | return none
          w.apart r other with
      | .inl proof =>
        let misses ← mkExpectedTypeHint proof (← mkAppM ``Changes.Misses #[c, low, high])
        return ← next (mkApp (mkConst ``MachineState.memory) earlier)
          (← mkAppOptM ``MachineState.Except.same #[state, earlier, c, kept, r, misses])
      | .inr range => stop := stop <|> some do
        let where_ := m!"stopped at the nested block that ended in {← describe state}: "
        let some other := (← instantiateMVars range).app1? ``Region.range
          | return (m!"{where_}its change lists the range{indentExpr range}\nwhich is not a region.", false)
        if (← Places.inside? r other).isSome then
          return (m!"{where_}`{r}` lies in `{other}`, which its change lists, so only its \
            postcondition says what `{r}` holds after it. State what you need there.", false)
        return (m!"{where_}its change lists `{other}`. {← notApart r other}", false)
    if stop.isSome then return (memory, none, stop)
  return (memory, none, none)

-- A placed read at a store it did not pass by its region. When the two pointers are a literal number of
-- bytes apart, what the laws ask is evaluated: the read misses the store, or is bytes of the value stored.
meta partial def Walk.atStore (w : Walk) (read memory address size : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some (earlier, base, length, bytes, fact?) ← store? w.history memory | return none
  let some (distance, place) ← Places.between? address base | return none
  let (some bytesRead, some bytesStored) := (← getNatValue? size, ← getNatValue? length) | return none
  let some (_, placed) := (← w.placements base length)[0]? | return none
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
    let outside ← mkAppM ``Region.Has.apart #[read, placed, ← place, after, before]
    let proof ← mkAppM ``Memory.readBytes_storeBytes_outside #[earlier, bytes, outside, ← mkAppM ``Region.Has.fits #[read]]
    return some (mkApp3 (mkConst ``readBytes) earlier address size, ← renamed proof)
  unless 0 < bytesRead && distance + bytesRead ≤ bytesStored do return none
  let_expr littleEndianAt _ value anchor := bytes | return none
  unless anchor == base do return none
  let within ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit distance, length])
  let inside ← mkDecideProof (← le (← sum (mkNatLit distance) size) length)
  let start ← mkAppM ``Region.Has.toNat_past #[placed, ← place, within]
  let proof ← mkAppM ``Region.Has.readBytes_stored #[placed, mkNatLit distance, start, inside, earlier, value]
  return some ((← inferType proof).eq?.get!.2.2, ← renamed proof)

private meta partial def Walk.region (w : Walk) (r memory : Expr) : MetaM (Expr × Option Expr) := do
  let key := (r, memory)
  if let some hit := (← w.regions.get)[key]? then return hit
  let (earlier, step?, _) ← w.regionStep r memory
  let result ← match step? with
    | some step => do
      let (first, rest?) ← w.region r earlier
      match rest? with
      | some rest => pure (first, some (← mkAppM ``Region.Same.trans #[rest, step]))
      | none => pure (earlier, some step)
    | none => pure (memory, none)
  w.regions.modify (·.insert key result)
  return result

meta partial def Walk.walk (w : Walk) (e : Expr) (limit : Nat := w.count) : MetaM Simp.Result := do
  if let some result := (← w.answers.get)[(limit, e)]? then return result
  let procs := w.reductions.push (({} : Simp.Simprocs).addCore #[.star] `rivetLocation false (.inl fun sub => do
    if sub != e && !sub.hasLooseBVars && (location? sub).isSome then return .done (← w.walk sub limit)
    if let some (rhs, proof) := w.history.equations[sub]? then return .visit { expr := rhs, proof? := some proof }
    if (registerFile? sub).isSome then
      if let some result ← w.select sub then return .visit result
      return ← unchangedRegister w.history sub
    return ← unchangedKernel w.history sub))
  let procs := procs.push (({} : Simp.Simprocs).addCore #[.star] `rivetValue true (.inl fun sub => do
    let some _ := location? sub | return .continue
    if sub.hasLooseBVars then return .continue
    if let some (memory, address, size) := sub.app3? ``readBytes then
      if moves w.history memory then
        for (r, placed) in ← w.placements address size do
          if let (earlier, some same) ← w.region r memory then
            return .visit { expr := mkApp3 (mkConst ``readBytes) earlier address size, proof? := some (← mkEqSymm (← mkAppM ``Region.Same.read #[same, placed])) }
          if let some (value, proof) ← w.atStore placed memory address size then
            return .visit { expr := value, proof? := some proof }
    for (rank, source, lhs, rhs) in w.candidates[bucket sub]?.getD #[] do
      if rank ≥ limit then break
      let mut proof := source
      if let some (memory, addr, size) := lhs.app3? ``readBytes then
        unless ← Places.same (sub.getArg! 2) size do continue
        let pointer ← w.walk addr rank
        unless ← Places.same pointer.expr (sub.getArg! 1) do continue
        if let some equal := pointer.proof? then
          let f ← withLocalDeclD `p (← inferType addr) fun p =>
            mkLambdaFVars #[p] (mkApp3 (mkConst ``readBytes) memory p size)
          proof ← mkEqTrans (← mkEqSymm (← mkCongrArg f equal)) proof
      let right ← w.walk rhs rank
      if (right.expr.find? (· == sub)).isSome then
        w.skipped.modify (·.push (source, sub, m!"its value reads it again"))
        continue
      if let some equal := right.proof? then proof ← mkEqTrans proof equal
      w.used.modify (·.push (source, sub, right.expr))
      return .visit { expr := right.expr, proof? := some proof }
    return .continue))
  let result := (← Meta.simp e w.context procs).1
  let result := { result with expr := ← instantiateMVars result.expr }
  if !e.hasMVar && !result.expr.hasMVar then w.answers.modify (·.insert (limit, e) result)
  return result

meta partial def Walk.places (w : Walk) : MetaM (Array (Expr × Expr)) := do
  if let some known ← w.placeCache.get then return known
  let written := w.fields.filter fun (_, part) => !(Places.regions part).isEmpty
  let written := written ++ (← Places.rootPlaces (written.flatMap (Places.regions ·.2)))
  let mut known := written.flatMap fun fact => #[fact, fact]
  let mut pending := Array.range written.size
  repeat
    let snapshot := { w with
      placeCache := ← IO.mkRef (some known), answers := ← IO.mkRef {},
      readPlaces := ← IO.mkRef {}, regions := ← IO.mkRef {}, apartness := ← IO.mkRef {} }
    let mut retry := #[]
    let mut progress := false
    for i in pending do
      let (proof, type) := known[2*i+1]!
      let result ← snapshot.walk type
      if result.expr != type then
        let fact ← match result.proof? with
          | some equal => mkEqMP equal proof
          | none => mkExpectedTypeHint proof result.expr
        known := known.set! (2*i+1) (fact, result.expr)
        progress := true
      if (result.expr.find? fun e => (e.app3? ``readBytes).any fun (m, _, _) => moves w.history m).isSome then
        retry := retry.push i
    if !progress || retry.isEmpty then break
    pending := retry
  let mut seen : Std.HashSet Expr := {}
  let mut distinct := #[]
  for (proof, type) in known do
    unless seen.contains type do distinct := distinct.push (proof, type)
    seen := seen.insert type
  w.placeCache.set (some distinct)
  return distinct

end

meta def Walk.readBack (w : Walk) (goal : MVarId) (hypotheses : Array FVarId := #[]) (target := true) :
    MetaM (Option MVarId) := do
  let run : Simp.Simproc := fun e => return .done (← w.walk e)
  let procs := #[({} : Simp.Simprocs).addCore #[.star] `rivetWalk false (.inl run)]
  let (result, _) ← simpGoal goal (w.context.setFailIfUnchanged false) procs
    (simplifyTarget := target) (fvarIdsToSimp := hypotheses)
  return result.map (·.2)

meta def Walk.make (goal : MVarId) (except : Array FVarId := #[])
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) : TacticM Walk := goal.withContext do
  let history ← History.read
  let mut aliases : Std.HashSet FVarId := {}
  let mut lets : SimpTheorems := {}
  for id in history.lets do
    let value ← instantiateMVars (← id.getDecl).value
    if value.hasAnyFVar aliases.contains || (value.find? (location? · |>.isSome)).isSome then
      aliases := aliases.insert id
      lets := lets.addLetDeclToUnfold id
  let all := #[← `(Lean.Parser.Tactic.simpLemma| rivet), ← `(Lean.Parser.Tactic.simpLemma| BitVec.reduceToNat)] ++ extra
  let saved ← getGoals
  setGoals [goal]
  let { ctx, simprocs, .. } ← try mkSimpContext (← `(tactic| simp only [$all,*])) (eraseLocal := false)
    finally setGoals saved
  let ctx := ctx.setSimpTheorems (ctx.simpTheorems.push lets)
  let reductions := simprocs.push (({} : Simp.Simprocs).addCore #[.star] ``openAbbrev false (.inr (openAbbrev history.later)))
  let mut plain := #[]
  let mut low := #[]
  let mut reads := #[]
  let mut skipped := #[]
  let mut fields := #[]
  for decl in history.users do
    for (source, part) in ← ReadBack.parts decl.toExpr decl.type #[``Region.Has, ``Region.Apart, ``Kernel.Reads, ``Kernel.Writes] do
      fields := fields.push (source, part)
      if except.contains decl.fvarId then continue
      let some (_, lhs, rhs) := part.eq? | continue
      let mut lhs ← zetaDeltaFVars lhs history.lets
      while (location? lhs).isNone do
        let some name := lhs.getAppFn.constName? | break
        unless (← isReducible name) && !(← isProjectionFn name) do break
        let some unfolded ← unfoldDefinition? lhs | break
        lhs := unfolded.headBeta
      let some of := location? lhs
        | if (location? rhs).isSome then skipped := skipped.push (source, rhs, m!"a fact is written `location = value`")
          continue
      let state := (of.app1? ``MachineState.memory).getD of
      let register := if lhs.isAppOfArity ``BitVec.setWidth 3 then lhs.getArg! 2 else lhs
      let kept ← history.leaves register
      unless state.isFVar && !(← isStepState state) && !history.stores.contains state.fvarId! && kept.isNone do
        skipped := skipped.push (source, lhs, if state.isFVar then m!"the walk goes back past this state"
          else m!"the walk stops only at a state: the block's start, or a nested block's end")
        continue
      let candidate := (source, lhs, rhs)
      if lhs.isAppOfArity ``readBytes 3 then reads := reads.push candidate
      else if lhs.isAppOfArity ``BitVec.setWidth 3 then low := low.push candidate
      else plain := plain.push candidate
  let mut candidates := {}
  let ordered := plain ++ low ++ reads
  for ((source, lhs, rhs), rank) in ordered.zipIdx do
    let key := bucket lhs
    candidates := candidates.insert key ((candidates[key]?.getD #[]).push (rank, source, lhs, rhs))
  return { history, context := ctx, reductions, candidates, count := ordered.size, fields, answers := ← IO.mkRef {}, readPlaces := ← IO.mkRef {}, placeCache := ← IO.mkRef none, regions := ← IO.mkRef {}, apartness := ← IO.mkRef {}, used := ← IO.mkRef #[], skipped := ← IO.mkRef skipped }
meta def Walk.parts (w : Walk) : MetaM (Array (Expr × Expr)) :=
  w.fields.flatMapM fun (source, part) => do
    let bounds ← if part.isAppOfArity ``Region.Has 3 then ReadBack.parts source part else pure #[]
    return #[(source, part)] ++ bounds

-- For an error: the facts the walk of `asked` used that left a variable in `shown`, and the equations about
-- a location in either that are not facts.
meta def Walk.notes (w : Walk) (asked shown : Expr) : MetaM MessageData := do
  let fresh := { w with answers := ← IO.mkRef {}, used := ← IO.mkRef #[] }
  discard <| fresh.walk asked
  let mut notes := m!""
  let mut seen : Std.HashSet Expr := {}
  for (source, key, value) in ← fresh.used.get do
    if value.hasFVar && (shown.find? (· == value)).isSome && !seen.contains source then
      seen := seen.insert source
      notes := notes ++ m!"\n`{key}` is read as `{value}`, by `{source}`."
  for (source, location, why) in ← w.skipped.get do
    if [asked, shown].any (·.find? (· == location) |>.isSome) && !seen.contains source then
      seen := seen.insert source
      notes := notes ++ m!"\n`{source}` does not say what `{location}` holds: {why}."
  return notes

end ReadBack

end Rivet.Internal
