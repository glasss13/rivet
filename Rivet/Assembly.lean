module
public import Rivet.Parser
public meta import Rivet.Parser
public meta import Lean

namespace Rivet

public meta section
open Lean Meta Elab Term

deriving instance ToExpr for Reg
deriving instance ToExpr for Reg32
deriving instance ToExpr for Reg8
deriving instance ToExpr for Mem8
deriving instance ToExpr for Op
deriving instance ToExpr for Instruction

-- Lean 4.35's kernel decodes string literals quadratically. Reuse the proved
-- encode/decode identity instead of asking it to run the decoder again.
cbv_simproc ↓ stringCharacters (String.toList _) := fun expression => do
  let some value := Sym.getStringValue? (← whnf expression.appArg!) | return .rfl
  let characters ← Sym.share (toExpr value.toList)
  return .step characters (mkApp (mkConst ``String.toList_ofList) characters)

/-- Parse constant assembly once and retain a kernel-checked certificate of the result. -/
elab "assembly% " source:term : term => do
  let expression ← elabTermEnsuringType source (some (mkConst ``String))
  let some text := Sym.getStringValue? (← whnf expression) |
    throwErrorAt source "expected a constant assembly string"
  let program ← match Rivet.parse text with
    | .ok program => pure program
    | .error message => throwErrorAt source message
  let instructions ← exprToSyntax (← mkListLit (mkConst ``Instruction) (program.map toExpr))
  elabTerm (← `((⟨$instructions, by decide_cbv⟩ :
    { program : Program // parse $source = .ok program }).val)) (some (mkConst ``Program))

end
end Rivet
