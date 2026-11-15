module
public import Rivet.Laws.Regions
public import Rivet.Tactics.Registers
public meta import Lean
-- Where a pointer is, which regions are apart, and what the image grants: each a lookup among the
-- hypotheses as written, or in a layout's list, with literal offsets compared as numbers. Nothing
-- here asks arithmetic of the hypotheses.
public section
namespace Rivet
open Lean Meta

namespace Places

-- The same as written, through `abbrev`s.
meta def same (a b : Expr) : MetaM Bool := withNewMCtxDepth <| withReducible <| isDefEq a b

meta def literal? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some value ← getNatValue? e then return some value
  getNatValue? (← whnfD e)

-- A pointer a literal number of bytes into a region: the region, the offset, and the equation
-- `pointer = r.place offset`. The base is a hypothesis `r.At offset base`, as written; literals added
-- and subtracted fold.
meta partial def literalPlace? (pointer : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  let pointer ← instantiateMVars pointer
  if let some (r, offset) := pointer.app2? ``Region.place then
    let some offset ← getNatValue? offset | return none
    return some (r, offset, ← mkEqRefl pointer)
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr Region.At r offset base := ← instantiateMVars decl.type | continue
    unless base == pointer do continue
    let some value ← getNatValue? offset | continue
    return some (r, value, ← mkExpectedTypeHint decl.toExpr (← mkEq pointer (mkApp2 (mkConst ``Region.place) r offset)))
  let folded (base literal : Expr) (add : Bool) : MetaM (Option (Expr × Nat × Expr)) := do
    let some ⟨width, value⟩ ← getBitVecValue? literal | return none
    unless width == 64 do return none
    let some (r, offset, proof) ← literalPlace? base | return none
    if add then
      let sum := offset + value.toNat
      return some (r, sum, ← mkAppM ``Region.place_add #[proof, literal, mkNatLit sum, ← mkEqRefl (mkNatLit sum)])
    else
      if offset < value.toNat then return none
      let difference := offset - value.toNat
      return some (r, difference,
        ← mkAppM ``Region.place_sub #[proof, literal, mkNatLit difference, ← mkEqRefl (mkNatLit offset)])
  match_expr pointer with
  | HAdd.hAdd _ _ _ _ base literal => folded base literal true
  | HSub.hSub _ _ _ _ base literal => folded base literal false
  | _ => return none

-- Every layout in scope: its proof, its image, and the regions it names.
meta def layouts : MetaM (Array (Expr × Expr × Array Expr)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr Image.Layout image regions := ← whnfR (← instantiateMVars decl.type) | continue
    found := found.push (decl.toExpr, image, ← ReadBack.listItems regions)
  return found

-- `r.Apart other`: a hypothesis as written, either way round, or two entries of a layout.
meta def apart? (r other : Expr) : MetaM (Option Expr) := do
  let wanted := mkApp2 (mkConst ``Region.Apart) r other
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr Region.Apart first second := ← instantiateMVars decl.type | continue
    if (← same first r) && (← same second other) then return some decl.toExpr
    if (← same first other) && (← same second r) then return some (← mkAppM ``Region.Apart.symm #[decl.toExpr])
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
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity name 2 do continue
    if (← same (type.getArg! 0) image) && (← same (type.getArg! 1) r) then return some decl.toExpr
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

-- `r.Has pointer size`, where `r` may be unknown: a hypothesis as written (or one of more bytes at
-- the same pointer, both sizes literal), or a literal place inside `r`, or inside a region a layout
-- names. Returns the region with the proof.
meta def has? (r pointer size : Expr) : MetaM (Option (Expr × Expr)) := do
  let r ← instantiateMVars r
  let pointer ← instantiateMVars pointer
  let size ← instantiateMVars size
  let fits (candidate : Expr) : MetaM Bool := if r.isMVar then pure true else same candidate r
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr Region.Has candidate at_ length := ← instantiateMVars decl.type | continue
    unless at_ == pointer && (← fits candidate) do continue
    if length == size then return some (candidate, decl.toExpr)
    let (some wanted, some given) := (← getNatValue? size, ← getNatValue? length) | continue
    if wanted ≤ given then
      let le ← mkDecideProof (← mkAppM ``LE.le #[size, length])
      return some (candidate, ← mkAppM ``Region.Has.first #[decl.toExpr, le])
  let some (base, offset, equation) ← literalPlace? pointer | return none
  let some bytes ← getNatValue? size | return none
  if bytes == 0 then return none
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, size])
  let candidates ← if r.isMVar then pure ((← layouts).flatMap (·.2.2) |>.push base) else pure #[r]
  for candidate in candidates do
    let wanted := mkApp3 (mkConst ``Region.Has) candidate pointer size
    if ← same candidate base then
      let some length ← literal? (mkApp (mkConst ``Region.length) base) | continue
      unless offset + bytes ≤ length do continue
      let inside ← mkDecideProof (← mkAppM ``LE.le
        #[← mkAppM ``HAdd.hAdd #[mkNatLit offset, size], mkApp (mkConst ``Region.length) base])
      return some (candidate, ← mkExpectedTypeHint (← mkAppM ``Region.Has.of_place #[equation, inside, positive]) wanted)
    let_expr Region.part whole start length inside := ← whnfR candidate | continue
    unless ← same whole base do continue
    let (some first, some count) := (← literal? start, ← literal? length) | continue
    unless first ≤ offset && offset + bytes ≤ first + count do continue
    let low ← mkDecideProof (← mkAppM ``LE.le #[start, mkNatLit offset])
    let high ← mkDecideProof (← mkAppM ``LE.le
      #[← mkAppM ``HAdd.hAdd #[mkNatLit offset, size], ← mkAppM ``HAdd.hAdd #[start, length]])
    let proof ← mkAppOptM ``Region.Has.of_place_part
      #[whole, pointer, mkNatLit offset, size, start, length, inside, equation, low, high, positive]
    return some (candidate, ← mkExpectedTypeHint proof wanted)
  return none

-- The region an access is in, with its place: what a step proved of it, or a literal place.
meta def placed? (pointer size : Expr) : MetaM (Option (Expr × Expr)) := do
  has? (← mkFreshExprMVar (mkConst ``Region)) pointer size

-- For an error only: the regions named in scope, by a layout, a place, a permission or apartness.
meta def named : MetaM MessageData := do
  let mut found : Array Expr := #[]
  let mut candidates := (← layouts).flatMap (·.2.2)
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Region.Has 3 || type.isAppOfArity ``Region.At 3 then
      candidates := candidates.push (type.getArg! 0)
    if type.isAppOfArity ``Region.Apart 2 then candidates := candidates ++ #[type.getArg! 0, type.getArg! 1]
    if type.isAppOfArity ``Image.Reads 2 || type.isAppOfArity ``Image.Writes 2 then
      candidates := candidates.push (type.getArg! 1)
  for r in candidates do
    unless ← found.anyM (same · r) do found := found.push r
  if found.isEmpty then return m!"No region is named in scope: carry a layout, or state a place."
  return m!"The regions named in scope: {MessageData.joinSep (found.toList.map fun r => m!"`{r}`") ", "}."

end Places

end Rivet
