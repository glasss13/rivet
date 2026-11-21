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

-- The instruction `program.fetch` finds at `pc`: down the tree to one leaf, then along it.
private meta def fetched (program : Expr) (pc : Nat) : MetaM (Option Expr) := do
  let mut current ← whnf program
  while current.isAppOfArity ``Program.branch 3 do
    let some split ← addressValue? (current.getArg! 0) | return none
    current ← whnf (current.getArg! (if pc < split then 1 else 2))
  unless current.isAppOfArity ``Program.leaf 1 do return none
  current := current.getArg! 0
  repeat
    current ← whnf current
    unless current.isAppOfArity ``List.cons 3 do return none
    let instruction ← whnf (current.getArg! 1)
    unless instruction.isAppOfArity ``Instruction.mk 3 do return none
    let some address ← addressValue? (instruction.getArg! 0) | return none
    let some length ← (evalNat (← whnf (instruction.getArg! 1))).run | return none
    if address == pc && 0 < length && length ≤ 15 then return some instruction
    current := current.getArg! 2
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
  let some instruction ← fetched (← programOf original) pc | return none
  let result ← mkAppM ``Option.some #[instruction]
  -- State the result about the caller's program, so it matches their goal syntactically.
  let fetch ← mkAppM ``Program.fetch #[original, address]
  return some (instruction, ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq fetch result))

end Fetch

end Rivet.Internal
end
