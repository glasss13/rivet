module
public import Rivet.Laws.Regions
public import Rivet.Tactics.Registers
public meta import Lean
-- Pointers and regions, compared without arithmetic on the hypotheses. A pointer is placed by a
-- hypothesis `r.Has q n`. Two pointers that are one expression plus or minus literals are a literal
-- number of bytes apart, and what a place covers and whether two places meet is then evaluated. A
-- region is the same: two parts of one region at literal offsets are compared by evaluation, and a part
-- has what its region has. Otherwise that two regions are apart, and that the image grants one, are
-- hypotheses. A hypothesis about a later state is read back to the block's start, as a goal is.
public section
namespace Rivet
open Lean Meta

namespace Places

-- The same as written, through `abbrev`s.
meta def same (a b : Expr) : MetaM Bool := withNewMCtxDepth <| withReducible <| isDefEq a b

-- A pointer as an expression plus a literal: the expression, the literal, and the equation
-- `pointer = base + BitVec.ofNat 64 offset`. Literals added and subtracted fold; a literal pointer is
-- off `0#64`; any other pointer is itself plus zero.
meta partial def offset (pointer : Expr) : MetaM (Expr × Nat × Expr) := do
  let pointer ← instantiateMVars pointer
  if let some ⟨width, value⟩ ← getBitVecValue? pointer then
    if width == 64 then return (toExpr 0#64, value.toNat, mkApp (mkConst ``Offset.literal) pointer)
  let folded (inner literal : Expr) (law : Name) (sum : Nat → Nat → Nat) : MetaM (Option (Expr × Nat × Expr)) := do
    let some ⟨width, value⟩ ← getBitVecValue? literal | return none
    unless width == 64 do return none
    let (base, bytes, proof) ← offset inner
    let total := sum bytes value.toNat % 2^64
    return some (base, total, ← mkAppM law #[proof, literal, mkNatLit total, ← mkEqRefl (mkNatLit total)])
  let found ← match_expr pointer with
    | HAdd.hAdd _ _ _ _ base literal => folded base literal ``Offset.add (· + ·)
    | HSub.hSub _ _ _ _ base literal => folded base literal ``Offset.sub (fun bytes value => bytes + (2^64 - value))
    | _ => pure none
  return found.getD (pointer, 0, mkApp (mkConst ``Offset.refl) pointer)

-- How many bytes `pointer` is past `other`, as words, when both are off one expression: the number,
-- and the equation `pointer = other + BitVec.ofNat 64 distance`.
meta def between? (pointer other : Expr) : MetaM (Option (Nat × Expr)) := do
  let (base, bytes, placed) ← offset pointer
  let (otherBase, otherBytes, otherPlaced) ← offset other
  unless ← same base otherBase do return none
  let distance := (bytes + (2^64 - otherBytes)) % 2^64
  return some (distance, ← mkAppM ``Offset.between #[placed, otherPlaced, mkNatLit distance, ← mkEqRefl (mkNatLit bytes)])

-- What the hypotheses say of places, regions and the image: each such statement in scope, a record's
-- fields among them.
meta partial def known : MetaM (Array (Expr × Expr)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    found ← visit decl.toExpr decl.type found
  return found
where
  visit (proof type : Expr) (found : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let type ← instantiateMVars type
    let some name := type.getAppFn.constName? | return found
    if [``Region.Has, ``Region.Apart, ``Image.Reads, ``Image.Writes].contains name then
      return found.push (proof, type)
    if isStructure (← getEnv) name && (← isProp type) then
      return ← (getStructureFields (← getEnv) name).foldlM (init := found) fun found field => do
        let part ← mkProjection proof field
        visit part (← inferType part) found
    if ← isReducible name then
      let opened ← whnfR type
      if opened != type then return ← visit proof opened found
    return found

-- The statements about a later state, read back to the block's start as a goal is.
meta def readBack (statements : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  let later ← ReadBack.later
  let moved := statements.filter fun (_, type) => later.any (type.containsFVar ·)
  if moved.isEmpty then return #[]
  let types := moved.map (·.2)
  let tactic ← (ReadBack.registersBack (mkAndN types.toList)).run'
  let results ← IO.mkRef #[]
  discard <| (Elab.Tactic.run (← mkFreshExprMVar (mkConst ``True)).mvarId! do
    let { ctx, simprocs, .. } ← Elab.Tactic.mkSimpContext tactic (eraseLocal := false)
    for type in types do results.modify (·.push (← simp type ctx simprocs).1)).run'
  (moved.zip (← results.get)).filterMapM fun ((proof, type), result) => do
    if result.expr == type then return none
    return some (← match result.proof? with
      | some equal => mkEqMP equal proof
      | none => mkExpectedTypeHint proof result.expr, result.expr)

-- A lookup among the hypotheses as written, then among them read back.
meta def lookup (find : Array (Expr × Expr) → MetaM (Option α)) : MetaM (Option α) := do
  let known ← known
  if let some found ← find known then return some found
  find (← readBack known)

-- A region as a part of another, `r.part offset length` with literal offset and length, through
-- `abbrev`s: the region it is part of, the two numbers, and the proof it lies inside.
meta partial def part? (region : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let region := (← instantiateMVars region).headBeta
  if region.isAppOfArity ``Region.part 4 then
    let #[r, offset, length, inside] := region.getAppArgs | return none
    let (some _, some _) := (← getNatValue? offset, ← getNatValue? length) | return none
    return some (r, offset, length, inside)
  let some name := region.getAppFn.constName? | return none
  unless ← isReducible name do return none
  let some unfolded ← unfoldDefinition? region | return none
  part? unfolded

-- `r.Apart other`: a hypothesis, either way round; two parts of one region whose offsets do not meet;
-- or a part whose region is apart from the other.
meta partial def apart? (r other : Expr) : MetaM (Option Expr) := do
  let found ← lookup fun known => do
    for (proof, type) in known do
      let_expr Region.Apart first second := type | continue
      if (← same first r) && (← same second other) then return some proof
      if (← same first other) && (← same second r) then return some (← mkAppM ``Region.Apart.symm #[proof])
    return none
  if found.isSome then return found
  let left ← part? r
  let right ← part? other
  if let (some (root, offset, length, inside), some (root', offset', length', inside')) := (left, right) then
    if ← same root root' then
      let number (e : Expr) := return (← getNatValue? e).getD 0
      let (a, b, c, d) := (← number offset, ← number length, ← number offset', ← number length')
      unless a + b ≤ c || c + d ≤ a do return none
      let apart := mkOr (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[offset, length], offset'])
        (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[offset', length'], offset])
      return some (← mkAppOptM ``Region.part_apart #[root, offset, length, offset', length', inside, inside', ← mkDecideProof apart])
  if let some (root, offset, length, inside) := left then
    if let some proof ← apart? root other then
      return some (← mkAppM ``Region.Apart.part_left #[proof, offset, length, inside])
  if let some (root, offset, length, inside) := right then
    if let some proof ← apart? r root then
      return some (← mkAppM ``Region.Apart.part_right #[proof, offset, length, inside])
  return none

-- `image.Reads r` or `image.Writes r`: a hypothesis, or of the region `r` is a part of.
meta partial def grant? (writes : Bool) (image r : Expr) : MetaM (Option Expr) := do
  let name := if writes then ``Image.Writes else ``Image.Reads
  let found ← lookup fun known => do
    for (proof, type) in known do
      unless type.isAppOfArity name 2 do continue
      if (← same (type.getArg! 0) image) && (← same (type.getArg! 1) r) then return some proof
    return none
  if found.isSome then return found
  let some (root, offset, length, inside) ← part? r | return none
  let some proof ← grant? writes image root | return none
  return some (← mkAppM (if writes then ``Image.Writes.part else ``Image.Reads.part) #[proof, offset, length, inside])

-- `r.Has pointer size`, where `r` may be unknown: a hypothesis, or one that covers it: the pointer a
-- literal number of bytes past its own, and the literal bytes asked for inside those it has. Returns the
-- region with the proof.
meta def has? (r pointer size : Expr) : MetaM (Option (Expr × Expr)) := do
  let r ← instantiateMVars r
  let pointer ← instantiateMVars pointer
  let size ← instantiateMVars size
  let fits (candidate : Expr) : MetaM Bool := if r.isMVar then pure true else same candidate r
  lookup fun known => do
    for (proof, type) in known do
      let_expr Region.Has candidate at_ length := type | continue
      if at_ == pointer && length == size && (← fits candidate) then return some (candidate, proof)
    let some bytes ← getNatValue? size | return none
    if bytes == 0 then return none
    for (proof, type) in known do
      let_expr Region.Has candidate at_ length := type | continue
      let some room ← getNatValue? length | continue
      unless ← fits candidate do continue
      let some (distance, place) ← between? pointer at_ | continue
      unless distance + bytes ≤ room do continue
      let inside ← mkDecideProof (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit distance, size], length])
      let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, size])
      return some (candidate, ← mkAppM ``Region.Has.cover #[proof, place, inside, positive])
    return none

-- The region an access is in, with its place.
meta def placed? (pointer size : Expr) : MetaM (Option (Expr × Expr)) := do
  has? (← mkFreshExprMVar (mkConst ``Region)) pointer size

-- For an error only: the regions named in scope, by a place, a permission or apartness.
meta def named : MetaM MessageData := do
  let mut found : Array Expr := #[]
  let mut candidates := #[]
  for (_, type) in ← known do
    match_expr type with
    | Region.Has r _ _ => candidates := candidates.push r
    | Region.Apart r other => candidates := candidates ++ #[r, other]
    | Image.Reads _ r => candidates := candidates.push r
    | Image.Writes _ r => candidates := candidates.push r
    | _ => pure ()
  for r in candidates do
    unless ← found.anyM (same · r) do found := found.push r
  if found.isEmpty then return m!"No region is named in scope."
  return m!"The regions named in scope: {MessageData.joinSep (found.toList.map fun r => m!"`{r}`") ", "}."

end Places

end Rivet
