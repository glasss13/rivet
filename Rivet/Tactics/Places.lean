module
public import Rivet.Laws.Regions
public import Rivet.Tactics.Registers
public meta import Lean
-- Where bytes are, compared without arithmetic on the hypotheses. Bytes are a range of a region: a region
-- cut from a root through parts at literal offsets is that many bytes into it. Two ranges are asked one
-- thing: is one inside the other, or are they apart? A pointer is placed by a hypothesis `r.Has q n`, or a
-- root where it starts; two pointers that are one expression plus or minus literals are a literal number
-- of bytes apart. That two regions are apart, and that the kernel grants one, are otherwise hypotheses.
public section
namespace Rivet.Internal
open Lean Meta

namespace Places

-- The same as written, through `abbrev`s.
meta def same (a b : Expr) : MetaM Bool := withNewMCtxDepth <| withReducible <| isDefEq a b

-- A pointer as an expression plus a literal: the expression, the literal, and how to prove
-- `pointer = base + BitVec.ofNat 64 offset`. Literals added and subtracted fold; a literal pointer is
-- off `0#64`; any other pointer is itself plus zero. Here, and below, the numbers are compared first and
-- only the answer is proved.
meta partial def offset (pointer : Expr) : MetaM (Expr × Nat × MetaM Expr) := do
  let pointer ← instantiateMVars pointer
  if let some ⟨width, value⟩ ← getBitVecValue? pointer then
    if width == 64 then return (toExpr 0#64, value.toNat, pure (mkApp (mkConst ``Offset.literal) pointer))
  let folded (inner literal : Expr) (law : Name) (sum : Nat → Nat → Nat) :
      MetaM (Option (Expr × Nat × MetaM Expr)) := do
    let some ⟨width, value⟩ ← getBitVecValue? literal | return none
    unless width == 64 do return none
    let (base, bytes, proof) ← offset inner
    let total := sum bytes value.toNat % 2^64
    return some (base, total, do mkAppM law #[← proof, literal, mkNatLit total, ← mkEqRefl (mkNatLit total)])
  let found ← match_expr pointer with
    | HAdd.hAdd _ _ _ _ base literal => folded base literal ``Offset.add (· + ·)
    | HSub.hSub _ _ _ _ base literal => folded base literal ``Offset.sub (fun bytes value => bytes + (2^64 - value))
    | _ => pure none
  if let some found := found then return found
  -- Through an `abbrev`: `frameBase a` may be `a.stackPointer - 16624#64`.
  if let some name := pointer.getAppFn.constName? then
    if (← isReducible name) && !(← isProjectionFn name) then
      if let some unfolded ← unfoldDefinition? pointer then
        let (base, bytes, proof) ← offset unfolded.headBeta
        return (base, bytes, do
          let proof ← proof
          mkExpectedTypeHint proof (← mkEq pointer (← inferType proof).eq?.get!.2.2))
  return (pointer, 0, pure (mkApp (mkConst ``Offset.refl) pointer))

-- How many bytes `pointer` is past `other`, as words, when both are off one expression: the number,
-- and the equation `pointer = other + BitVec.ofNat 64 distance`.
meta def between? (pointer other : Expr) : MetaM (Option (Nat × MetaM Expr)) := do
  let (base, bytes, placed) ← offset pointer
  let (otherBase, otherBytes, otherPlaced) ← offset other
  unless ← same base otherBase do return none
  let distance := (bytes + (2^64 - otherBytes)) % 2^64
  return some (distance, do mkAppM ``Offset.between #[← placed, ← otherPlaced, mkNatLit distance, ← mkEqRefl (mkNatLit bytes)])

-- The regions a statement names.
meta def regions (type : Expr) : Array Expr :=
  match_expr type with
  | Region.Has r _ _ => #[r]
  | Region.Apart r other => #[r, other]
  | Kernel.Reads _ r => #[r]
  | Kernel.Writes _ r => #[r]
  | _ => #[]

-- A region as a part of another, `r.part offset length`, through `abbrev`s: the region it is part of,
-- the two numbers, and the proof it lies inside.
meta partial def part? (region : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let region := (← instantiateMVars region).headBeta
  if region.isAppOfArity ``Region.part 4 then
    let #[r, offset, length, inside] := region.getAppArgs | return none
    return some (r, offset, length, inside)
  let some name := region.getAppFn.constName? | return none
  unless ← isReducible name do return none
  let some unfolded ← unfoldDefinition? region | return none
  part? unfolded

-- A region as a root, `Region.root start length readable writable fits`, through `abbrev`s.
meta partial def root? (region : Expr) : MetaM (Option (Array Expr)) := do
  let region := (← instantiateMVars region).headBeta
  if region.isAppOfArity ``Region.root 5 then return some region.getAppArgs
  let some name := region.getAppFn.constName? | return none
  unless ← isReducible name do return none
  let some unfolded ← unfoldDefinition? region | return none
  root? unfolded

-- A region's length as its constructor was given it, and how to prove `r.length = n`.
meta def length? (r : Expr) : MetaM (Option (Expr × MetaM Expr)) := do
  let law ← match ← part? r with
    | some (root, offset, length, inside) => pure (some (length, mkAppM ``Region.part_length #[root, offset, length, inside]))
    | none => match ← root? r with
      | some args => pure (some (args[1]!, mkAppM ``Region.root_length args))
      | none => pure none
  let some (length, law) := law | return none
  return some (length, do mkExpectedTypeHint (← law) (← mkEq (mkApp (mkConst ``Region.length) r) length))

-- Where a region's bytes are: the region it is cut from through parts at literal offsets, how many bytes
-- into it, and how to prove `r.At stem offset`.
meta partial def stem (r : Expr) : MetaM (Expr × Nat × MetaM Expr) := do
  if let some (parent, offset, length, inside) ← part? r then
    if let some bytes ← getNatValue? offset then
      let (root, before, at_) ← stem parent
      let sum := mkNatLit (before + bytes)
      return (root, before + bytes, do mkAppM ``Region.At.part #[← at_, offset, length, inside, sum, ← mkEqRefl sum])
  return (r, 0, mkAppM ``Region.At.refl #[r])

-- Two ranges of one region, as numbers: the offsets, the lengths, and how to prove the four facts the laws take.
meta def ranges? (a b : Expr) : MetaM (Option (Nat × Nat × Nat × Nat × MetaM (Array Expr))) := do
  let (stemA, i, atA) ← stem a
  let (stemB, j, atB) ← stem b
  unless ← same stemA stemB do return none
  let (some (n, lengthA), some (m, lengthB)) := (← length? a, ← length? b) | return none
  let (some n, some m) := (← getNatValue? n, ← getNatValue? m) | return none
  return some (i, n, j, m, return #[← atA, ← atB, ← lengthA, ← lengthB])

-- `a`'s bytes lie in `b`: two ranges of one region, by their numbers, or a part of a region inside `b`.
meta partial def inside? (a b : Expr) : MetaM (Option Expr) := do
  if ← same a b then return some (← mkAppM ``Region.Inside.refl #[a])
  if let some (i, n, j, m, proofs) ← ranges? a b then
    if j ≤ i && i + n ≤ j + m then
      let fits := mkAnd (← mkAppM ``LE.le #[mkNatLit j, mkNatLit i])
        (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit i, mkNatLit n], ← mkAppM ``HAdd.hAdd #[mkNatLit j, mkNatLit m]])
      return some (← mkAppM ``Region.Inside.of_at ((← proofs).push (← mkDecideProof fits)))
  let some (parent, offset, length, inside) ← part? a | return none
  let some rest ← inside? parent b | return none
  return some (← mkAppM ``Region.Inside.trans #[← mkAppM ``Region.Inside.part #[parent, offset, length, inside], rest])

-- `r.Apart other`: two ranges of one region that do not meet, by their numbers; or a hypothesis, either way
-- round, about regions the two lie in.
meta def apart? (known : Array (Expr × Expr)) (r other : Expr) : MetaM (Option Expr) := do
  if let some (i, n, j, m, proofs) ← ranges? r other then
    if i + n ≤ j || j + m ≤ i then
      let sum (a b : Nat) := mkAppM ``HAdd.hAdd #[mkNatLit a, mkNatLit b]
      let apart := mkOr (← mkAppM ``LE.le #[← sum i n, mkNatLit j]) (← mkAppM ``LE.le #[← sum j m, mkNatLit i])
      return some (← mkAppM ``Region.Apart.of_at ((← proofs).push (← mkDecideProof apart)))
  for (proof, type) in known do
    let_expr Region.Apart first second := type | continue
    if let (some left, some right) := (← inside? r first, ← inside? other second) then
      return some (← mkAppM ``Region.Apart.inside #[proof, left, right])
    if let (some left, some right) := (← inside? r second, ← inside? other first) then
      return some (← mkAppM ``Region.Apart.inside #[← mkAppM ``Region.Apart.symm #[proof], left, right])
  return none

-- `kernel.Reads r` or `kernel.Writes r`: a hypothesis about a region `r` lies in.
meta def grant? (known : Array (Expr × Expr)) (writes : Bool) (kernel r : Expr) : MetaM (Option Expr) := do
  for (proof, type) in known do
    let isReads := !writes && type.isAppOfArity ``Kernel.Reads 2
    let isWrites := type.isAppOfArity ``Kernel.Writes 2
    unless isReads || isWrites do continue
    unless ← same (type.getArg! 0) kernel do continue
    if let some inside ← inside? r (type.getArg! 1) then
      if writes then
        return some (← mkAppM ``Kernel.Writes.inside #[proof, inside])
      else if isWrites then
        return some (← mkAppM ``Kernel.Reads.inside #[← mkAppM ``Kernel.Writes.reads #[proof], inside])
      else
        return some (← mkAppM ``Kernel.Reads.inside #[proof, inside])
  return none

-- A root is placed where it starts: the place for the root of each region.
meta def rootPlaces (regions : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut roots : Std.HashSet Expr := {}
  let mut found := #[]
  for r in regions do
    let root := (← stem r).1
    let some args ← root? root | continue
    let key := mkAppN (mkConst ``Region.root) (args.extract 0 4)
    if roots.contains key then continue
    roots := roots.insert key
    let place := mkApp3 (mkConst ``Region.Has) root args[0]! args[1]!
    found := found.push (← mkExpectedTypeHint (← mkAppM ``Region.root_has args) place, place)
  return found

-- Each place that has the access, in scope order, with its region: a place `r.Has q m` with that pointer and
-- size, or one that covers it, the pointer a literal number of bytes past its own. A place that fills its
-- region puts the access in exactly those bytes of it, a part.
meta def places (known : Array (Expr × Expr)) (pointer size : Expr) : MetaM (Array (Expr × Expr)) := do
  let pointer ← instantiateMVars pointer
  let size ← instantiateMVars size
  let bytes? ← getNatValue? size
  let mut found := #[]
  for (proof, type) in known do
    let_expr Region.Has candidate at_ length := type | continue
    if (← same at_ pointer) && (← same length size) then found := found.push (candidate, proof); continue
    let some bytes := bytes? | continue
    if bytes == 0 then continue
    let some room := (← getNatValue? length) <|> (← getNatValue? (← whnfR length)) | continue
    let some (distance, place) ← between? pointer at_ | continue
    unless distance + bytes ≤ room do continue
    let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, size])
    let sum ← mkAppM ``HAdd.hAdd #[mkNatLit distance, size]
    if let some (written, law) ← length? candidate then
      if ← same written length then
        let law ← law
        let filled ← mkExpectedTypeHint (← mkAppM ``Nat.le_of_eq #[law])
          (← mkAppM ``LE.le #[mkApp (mkConst ``Region.length) candidate, length])
        let inside ← mkAppM ``Nat.le_trans #[← mkDecideProof (← mkAppM ``LE.le #[sum, written]),
          ← mkAppM ``Nat.le_of_eq #[← mkEqSymm law]]
        let exact ← mkAppM ``Region.Has.exact #[proof, filled, ← place, inside, positive]
        let_expr Region.Has part _ _ := ← inferType exact | continue
        found := found.push (part, exact)
        continue
    let inside ← mkDecideProof (← mkAppM ``LE.le #[sum, length])
    found := found.push (candidate, ← mkAppM ``Region.Has.cover #[proof, ← place, inside, positive])
  return found

-- `r.Has pointer size`: a place of the access in bytes inside `r`; or, for a part of a region at any offset,
-- its offset past a place that fills the region.
meta def has? (known : Array (Expr × Expr)) (r pointer size : Expr) : MetaM (Option Expr) := do
  let r ← instantiateMVars r
  let known := known ++ (← rootPlaces #[r])
  for (region, proof) in ← places known pointer size do
    if let some inside ← inside? region r then return some (← mkAppM ``Region.Has.inside #[proof, inside])
  let some (parent, offset, length, inside) ← part? r | return none
  unless (← getNatValue? length).any (0 < ·) && (← same length size) do return none
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, length])
  let whole := mkApp (mkConst ``Region.length) parent
  let written? ← length? parent
  for (proof, type) in known ++ (← rootPlaces #[parent]) do
    let_expr Region.Has candidate _ filled := type | continue
    unless ← same candidate parent do continue
    let fills ← if ← same filled whole then mkAppM ``Nat.le_refl #[whole] else
      let some (written, law) := written? | continue
      unless ← same filled written do continue
      mkExpectedTypeHint (← mkAppM ``Nat.le_of_eq #[← law]) (← mkAppM ``LE.le #[whole, filled])
    let place ← mkAppM ``Region.Has.part_at #[proof, fills, offset, length, inside, positive]
    let_expr Region.Has _ placed _ := ← inferType place | continue
    if placed == pointer then return some place
  return none

-- For an error only: the regions named in scope, by a place, a permission or apartness.
meta def named (known : Array (Expr × Expr)) : MetaM MessageData := do
  let mut found : Array Expr := #[]
  for r in known.flatMap (regions ·.2) do
    unless ← found.anyM (same · r) do found := found.push r
  if found.isEmpty then return m!"No region is named in scope."
  return m!"The regions named in scope: {MessageData.joinSep (found.toList.map fun r => m!"`{r}`") ", "}."

end Places

end Rivet.Internal
