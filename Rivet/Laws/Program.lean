module
public import Rivet.Interpreter.Syntax
-- Proof-only notions about programs: instruction evidence.
@[expose] public section
namespace Rivet
abbrev InstructionAt (program : Program) (address : BitVec 64) (length : Nat) (operation : Op) : Prop :=
  program.fetch address = some ⟨address, length, operation⟩

end Rivet
