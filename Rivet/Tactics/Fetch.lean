module
public import Rivet.Interpreter.Decode
public meta import Rivet.Interpreter.Decode
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

meta section
deriving instance ToExpr for Reg
deriving instance ToExpr for Reg8
deriving instance ToExpr for Reg16
deriving instance ToExpr for Reg32
deriving instance ToExpr for Width
deriving instance ToExpr for Scale
deriving instance ToExpr for Address
deriving instance ToExpr for Operand
deriving instance ToExpr for Condition
deriving instance ToExpr for BinaryOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for Xmm
deriving instance ToExpr for XmmMove
deriving instance ToExpr for Op

def prove (code address : Expr) (pc : Nat) : MetaM (Option (Expr × Expr)) := withTransparency .all do
  let mut front : DecodeState := .opcode {}
  for offset in [:15] do
    let atByte := toExpr (BitVec.ofNat 64 (pc + offset))
    let found ← whnf (mkApp code atByte)
    unless found.isAppOfArity ``Option.some 2 do return none
    let some n ← getNatValue? (← whnf (← mkAppM ``Fin.val #[found.getArg! 1])) | return none
    match feed front (Fin.ofNat 256 n) with
    | .reject => return none
    | .more next => front := next
    | .done finish =>
      let op := finish (BitVec.ofNat 64 (pc + offset + 1))
      let result := toExpr (some (offset + 1, op))
      let fetch := mkApp2 (mkConst ``Code.fetch) code address
      return some (toExpr op, ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq fetch result))
  return none
end

end Fetch

end Rivet.Internal
end
