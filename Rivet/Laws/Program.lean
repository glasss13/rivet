module
public import Rivet.Interpreter.Syntax
-- Proof-only notions about programs: instruction evidence and fetch suffixes.
@[expose] public section
namespace Rivet
abbrev InstructionAt (program : Program) (address : BitVec 64) (length : Nat) (operation : Op) : Prop :=
  program.fetch address = some ⟨address, length, operation⟩

-- Rivet's tactics build proofs with these, and the importer states its program with them. Proofs
-- never name them.
namespace Internal

def Program.FetchesFrom (program suffix : Program) (address : BitVec 64) : Prop :=
  ∀ other, address ≤ other → program.fetch other = suffix.fetch other

theorem Program.FetchesFrom.skip {program rest : Program} {instruction : Instruction} {next : BitVec 64}
    (previous : Program.FetchesFrom program (instruction :: rest) instruction.address)
    (increasing : instruction.address < next) : Program.FetchesFrom program rest next := by
  intro other bound
  have differs : (instruction.address == other) = false := by simp; bv_omega
  rw [previous other (by bv_omega)]
  simp [Program.fetch, differs]

end Internal

end Rivet
