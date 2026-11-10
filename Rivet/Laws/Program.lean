module
public import Rivet.Interpreter.Syntax
-- Proof-only notions about programs: instruction evidence, fetch suffixes, and register writes.
@[expose] public section
namespace Rivet
/-- Whether an instruction can write a register, including implicit RSP updates. -/
def modifies (operation : Op) (register : Reg) : Bool :=
  let writes : Operand → Bool
    | .reg8 destination | .reg16 destination | .reg32 destination => destination.parent == register
    | .reg64 destination => destination == register
    | .memory .. | .immediate _ => false
  match operation with
  | .binary operation destination _ => operation != .cmp && operation != .test && writes destination
  | .shift _ destination _ | .imul destination _ _ | .not destination | .mov destination _
  | .setcc _ destination | .cmovcc _ destination _ => writes destination
  | .movzx destination _ => destination.parent == register
  | .lea destination _ | .movsxd destination _ | .inc destination | .dec destination => destination == register
  | .pop destination => register == .rsp || destination == register
  | .push _ | .call _ | .ret => register == .rsp
  | .nop | .movd .. | .pshufd .. | .loadXmm .. | .storeXmm .. | .jmp _ | .jcc .. => false

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
