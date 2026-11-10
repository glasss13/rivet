module
public import Rivet.Interpreter.Syntax
-- Proof-only notions about programs: instruction evidence and fetch suffixes.
@[expose] public section
namespace Rivet
/-- The instruction at `address` has `length` and `operation`. Execution continues at
`address + length` unless the operation transfers control. -/
abbrev InstructionAt (program : Program) (address : BitVec 64) (length : Nat) (operation : Op) : Prop :=
  program.fetch address = some ⟨address, length, operation⟩

/-- At and above `address`, `program` fetches as `suffix` does. Generated programs
state this once per instruction, so any instruction is found in constant time. -/
def Program.FetchesFrom (program suffix : Program) (address : BitVec 64) : Prop :=
  ∀ other, address ≤ other → program.fetch other = suffix.fetch other

/-- Above a suffix's first instruction, the rest of the suffix takes over. -/
theorem Program.FetchesFrom.skip {program rest : Program} {instruction : Instruction} {next : BitVec 64}
    (previous : program.FetchesFrom (instruction :: rest) instruction.address)
    (increasing : instruction.address < next) : program.FetchesFrom rest next := by
  intro other bound
  have differs : (instruction.address == other) = false := by simp; bv_omega
  rw [previous other (by bv_omega)]
  simp [Program.fetch, differs]
end Rivet
