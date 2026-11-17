module
public import Rivet.Interpreter.Memory
public import Rivet.Laws.Program
-- Proves which instruction a concrete program holds at an address, for `rivet_step`.
public meta import Lean
public section
namespace Rivet.Internal
open Lean Meta Elab Tactic

namespace Fetch

meta def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

meta def addressValue? (address : Expr) : MetaM (Option Nat) := do
  let address ← instantiateMVars address
  if let some ⟨_, value⟩ ← getBitVecValue? address then return some value.toNat
  if address.hasFVar || address.hasMVar then return none
  try
    let value ← withTransparency .default <| whnf (← mkAppM ``BitVec.toNat #[address])
    (evalNat value).run
  catch _ => return none

private meta def firstMatch (list : Expr) (pc : Nat) (limit : Nat := 0) : MetaM (Option Expr) := do
  let mut current := list
  let mut visited := 0
  repeat
    if limit != 0 && visited ≥ limit then return none
    current ← whnf current
    unless current.isAppOfArity ``List.cons 3 do return none
    let instruction ← whnf (current.getArg! 1)
    unless instruction.isAppOfArity ``Instruction.mk 3 do return none
    let some address ← addressValue? (instruction.getArg! 0) | return none
    let some length ← (evalNat (← whnf (instruction.getArg! 1))).run | return none
    if address == pc && 0 < length && length ≤ 15 then return some instruction
    current := current.getArg! 2
    visited := visited + 1
  return none

private meta def programOf (program : Expr) : MetaM Expr := do
  let program ← instantiateMVars program
  let image? := if program.isAppOfArity ``Image.program 1 then some program.appArg!
    else match program with
      | .proj ``Image 0 image => some image
      | _ => none
  let some image := image? | return program
  let image ← whnfD image
  return if image.isAppOfArity ``Image.mk 2 then image.getArg! 0 else program

meta def prove (original address : Expr) (pc : Nat) : MetaM (Option (Expr × Expr)) := withTransparency .all do
  let program ← programOf original
  -- State the result about the caller's program, so it matches their goal syntactically.
  let restate (instruction proof : Expr) : MetaM (Expr × Expr) := do
    let fetched ← mkAppM ``Program.fetch #[original, address]
    return (instruction, ← mkExpectedTypeHint proof (← mkEq fetched (← mkAppM ``Option.some #[instruction])))
  if let some name := program.constName? then
    let stepName := name ++ Name.mkSimple s!"from_{hex pc}"
    if (← getEnv).contains stepName then
      let same := mkApp2 (mkConst stepName) address (mkApp2 (mkConst ``BitVec.le_refl) (mkNatLit 64) address)
      let some (_, _, suffixFetch) := (← instantiateMVars (← inferType same)).eq? | return none
      let some instruction ← firstMatch (suffixFetch.appFn!.appArg!) pc (limit := 1) | return none
      let result ← mkAppM ``Option.some #[instruction]
      let head ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq suffixFetch result)
      return some (← restate instruction (← mkEqTrans same head))
  let some instruction ← firstMatch program pc | return none
  let result ← mkAppM ``Option.some #[instruction]
  let fetched ← mkAppM ``Program.fetch #[program, address]
  return some (← restate instruction (← mkExpectedTypeHint (← mkEqRefl result) (← mkEq fetched result)))

end Fetch

end Rivet.Internal
end
