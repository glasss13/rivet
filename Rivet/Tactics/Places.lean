module
public import Rivet.Laws.Regions
public import Rivet.Tactics.Registers
public meta import Lean
-- Pointers and regions, compared without arithmetic on the hypotheses. Two pointers that are one
-- expression plus or minus literals are a literal number of bytes apart. A pointer is placed by a
-- hypothesis `r.Has q n` that covers it. Two regions are apart, and the image grants one, by a
-- hypothesis as written or a layout's list.
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
    if [``Region.Has, ``Region.Apart, ``Image.Layout, ``Image.Reads, ``Image.Writes].contains name then
      return found.push (proof, type)
    if isStructure (← getEnv) name && (← isProp type) then
      return ← (getStructureFields (← getEnv) name).foldlM (init := found) fun found field => do
        let part ← mkProjection proof field
        visit part (← inferType part) found
    if ← isReducible name then
      let opened ← whnfR type
      if opened != type then return ← visit proof opened found
    return found

-- Every layout in scope: its proof, its image, and the regions it names.
meta def layouts : MetaM (Array (Expr × Expr × Array Expr)) := do
  (← known).filterMapM fun (proof, type) => do
    let_expr Image.Layout image regions := type | return none
    return some (proof, image, ← ReadBack.listItems regions)

-- `r.Apart other`: a hypothesis as written, either way round, or two entries of a layout.
meta def apart? (r other : Expr) : MetaM (Option Expr) := do
  let wanted := mkApp2 (mkConst ``Region.Apart) r other
  for (proof, type) in ← known do
    let_expr Region.Apart first second := type | continue
    if (← same first r) && (← same second other) then return some proof
    if (← same first other) && (← same second r) then return some (← mkAppM ``Region.Apart.symm #[proof])
  for (layout, _, regions) in ← layouts do
    let some i ← regions.findIdxM? (same · r) | continue
    let some j ← regions.findIdxM? (same · other) | continue
    if i == j then continue
    let list ← mkListLit (mkConst ``Region) regions.toList
    let length ← mkAppM ``List.length #[list]
    let first ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, length])
    let second ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit j, length])
    let differ ← mkDecideProof (mkNot (← mkEq (mkNatLit i) (mkNatLit j)))
    return some (← mkExpectedTypeHint
      (← mkAppOptM ``Image.Layout.apart_at #[none, list, layout, mkNatLit i, mkNatLit j, first, second, differ]) wanted)
  return none

-- `image.Reads r` or `image.Writes r`: a hypothesis as written, or an entry of a layout that has
-- the permission.
meta def grant? (writes : Bool) (image r : Expr) : MetaM (Option Expr) := do
  let name := if writes then ``Image.Writes else ``Image.Reads
  let wanted := mkApp2 (mkConst name) image r
  for (proof, type) in ← known do
    unless type.isAppOfArity name 2 do continue
    if (← same (type.getArg! 0) image) && (← same (type.getArg! 1) r) then return some proof
  for (layout, layoutImage, regions) in ← layouts do
    unless ← same layoutImage image do continue
    let some i ← regions.findIdxM? (same · r) | continue
    let permission := mkApp (mkConst (if writes then ``Region.writable else ``Region.readable)) r
    unless (← whnfD permission).isConstOf ``true do continue
    let list ← mkListLit (mkConst ``Region) regions.toList
    let bound ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[list]])
    let law := if writes then ``Image.Layout.writes_at else ``Image.Layout.reads_at
    return some (← mkExpectedTypeHint
      (← mkAppOptM law #[none, list, layout, mkNatLit i, bound, ← mkEqRefl (mkConst ``true)]) wanted)
  return none

-- `r.Has pointer size`, where `r` may be unknown: a hypothesis as written, or one that covers it: its
-- pointer the same expression, and the literal bytes asked for inside the literal bytes it has.
-- Returns the region with the proof.
meta def has? (r pointer size : Expr) : MetaM (Option (Expr × Expr)) := do
  let r ← instantiateMVars r
  let pointer ← instantiateMVars pointer
  let size ← instantiateMVars size
  let fits (candidate : Expr) : MetaM Bool := if r.isMVar then pure true else same candidate r
  let known ← known
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

-- For an error only: the regions named in scope, by a layout, a place, a permission or apartness.
meta def named : MetaM MessageData := do
  let mut found : Array Expr := #[]
  let mut candidates := #[]
  for (_, type) in ← known do
    match_expr type with
    | Region.Has r _ _ => candidates := candidates.push r
    | Region.Apart r other => candidates := candidates ++ #[r, other]
    | Image.Reads _ r => candidates := candidates.push r
    | Image.Writes _ r => candidates := candidates.push r
    | Image.Layout _ regions => candidates := candidates ++ (← ReadBack.listItems regions)
    | _ => pure ()
  for r in candidates do
    unless ← found.anyM (same · r) do found := found.push r
  if found.isEmpty then return m!"No region is named in scope: carry a layout, or state a place."
  return m!"The regions named in scope: {MessageData.joinSep (found.toList.map fun r => m!"`{r}`") ", "}."

end Places

end Rivet
