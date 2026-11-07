module
public import Rivet.Parser
public meta import Rivet.Parser
public meta import Lean

namespace Rivet

public meta section
open Lean Meta Elab Term

deriving instance ToExpr for Reg
deriving instance ToExpr for Xmm
deriving instance ToExpr for XmmMove
deriving instance ToExpr for Reg32
deriving instance ToExpr for Reg8
deriving instance ToExpr for Reg16
deriving instance ToExpr for Width
deriving instance ToExpr for Scale
deriving instance ToExpr for Address
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for BinaryOp
deriving instance ToExpr for Operand
deriving instance ToExpr for Condition
deriving instance ToExpr for Op
deriving instance ToExpr for Instruction

-- Lean 4.35's kernel decodes string literals quadratically. Reuse the proved
-- encode/decode identity instead of asking it to run the decoder again.
cbv_simproc ↓ stringCharacters (String.toList _) := fun expression => do
  let some value := Sym.getStringValue? (← whnf expression.appArg!) | return .rfl
  let characters ← Sym.share (toExpr value.toList)
  return .step characters (mkApp (mkConst ``String.toList_ofList) characters)

/-- Parse constant assembly once and retain a kernel-checked certificate of the result. -/
elab "assembly% " source:term " at " base:term " with " sizes:term : term => do
  let expression ← elabTermEnsuringType source (some (mkConst ``String))
  let some text := Sym.getStringValue? (← whnf expression) |
    throwErrorAt source "expected a constant assembly string"
  let baseExpression ← elabTermEnsuringType base (some (mkConst ``Nat))
  let some baseAddress := (← whnf baseExpression).rawNatLit? |
    throwErrorAt base "expected a constant base address"
  let sizesType := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let mut sizesExpression ← elabTermEnsuringType sizes (some sizesType)
  let mut instructionLengths := []
  repeat
    sizesExpression ← whnf sizesExpression
    if sizesExpression.isAppOfArity ``List.nil 1 then break
    unless sizesExpression.isAppOfArity ``List.cons 3 do
      throwErrorAt sizes "expected a constant list of instruction lengths"
    let some size := (← whnf (sizesExpression.getArg! 1)).rawNatLit? |
      throwErrorAt sizes "expected constant instruction lengths"
    instructionLengths := size :: instructionLengths
    sizesExpression := sizesExpression.getArg! 2
  instructionLengths := instructionLengths.reverse
  let program ← match Rivet.parse text baseAddress instructionLengths with
    | .ok program => pure program
    | .error message => throwErrorAt source message
  let instructions ← exprToSyntax (← mkListLit (mkConst ``Instruction) (program.map toExpr))
  elabTerm (← `((⟨$instructions, by decide_cbv⟩ :
    { program : Program // parse $source $base $sizes = .ok program }).val)) (some (mkConst ``Program))

end
end Rivet
