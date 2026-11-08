module
public import Rivet.Contracts
public import Rivet.ExecutionProperties
@[expose] public section
namespace Rivet

abbrev InstructionAt (program : Program) (address : Nat) (instruction : Op) : Prop :=
  (program.fetch address).map Instruction.op = some instruction

-- Normalize known operand constructors without expanding unknown operands.
-- These equations already exist; only their simplification attributes are new.
attribute [simp] Operand.width.eq_1 Operand.width.eq_2 Operand.width.eq_3
  Operand.width.eq_4 Operand.width.eq_5 Operand.width.eq_6
  MachineState.readOperand.eq_1 MachineState.readOperand.eq_2 MachineState.readOperand.eq_3
  MachineState.readOperand.eq_4 MachineState.readOperand.eq_5 MachineState.readOperand.eq_6
  MachineState.writeOperand.eq_1 MachineState.writeOperand.eq_2 MachineState.writeOperand.eq_3
  MachineState.writeOperand.eq_4 MachineState.writeOperand.eq_5 MachineState.writeOperand.eq_6
  MachineState.canRead.eq_1 MachineState.canRead.eq_2
  MachineState.canWrite.eq_1 MachineState.canWrite.eq_2 MachineState.canWrite.eq_3
  MachineState.recordRead.eq_1 MachineState.recordRead.eq_2

@[simp] theorem MachineState.write_readHistory (state : MachineState) (register : Reg)
    (value : BitVec 64) : (state.write register value).readHistory = state.readHistory := rfl

private theorem one (code : InstructionAt program address instruction)
    (location : initial.status = .running address) (undefinedFlags : FlagValues) :
    step program initial undefinedFlags = stepOp instruction (program.nextAddress address) initial undefinedFlags := by
  simp only [step, location]
  cases entry : program.fetch address with
  | none => simp [InstructionAt, entry] at code
  | some found => simp [InstructionAt, entry] at code; simp [code, Program.nextAddress, entry]

-- Every instruction has the same contract shape as a multi-instruction block.
-- `code` is checked automatically for concrete programs, or supplied explicitly.
theorem clear (program : Program) (address : Nat) (destination : Reg32) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .xor (.reg32 destination) (.reg32 destination)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination.parent 0 with
      status := .running (program.nextAddress address), zeroFlag := true, carryFlag := false, signFlag := false }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance, MachineState.write]
  all_goals rfl

theorem test_zero (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .test (.reg64 register) (.reg64 register)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address), zeroFlag := initial.registers register == 0, carryFlag := false, signFlag := (initial.registers register).msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance]
  all_goals rfl

theorem read_byte (program : Program) (address : Nat) (destination : Reg32) (base : Reg) (initial : MachineState)
    (location : initial.status = .running address) (allowed : initial.memory.readable (initial.registers base).toNat = true)
    (code : InstructionAt program address (.movzx destination (.memory .byte { base := some base })) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination.parent (BitVec.ofNat 64 (initial.memory (initial.registers base).toNat).val) with
      status := .running (program.nextAddress address), readHistory := initial.readHistory ++ [⟨(initial.registers base).toNat,1⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have bound : (initial.registers base).toNat + 1 ≤ word := by
    have := (initial.registers base).isLt
    unfold word
    omega
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, Address.evaluate, Scale.value,
    Operand.width, MachineState.canRead, permits, MachineState.readOperand,
    readBytes, MachineState.recordRead] <;> try rfl
  have byte (value : Fin 256) :
      ({toFin := value} : BitVec 8).setWidth 64 = BitVec.ofNat 64 value.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rfl
  rw [byte]

/-- Successful ADD for every supported scalar width and operand form.
Concrete operand forms discharge unrelated validity and access obligations by
normalization; only encoding bounds and actual memory permissions remain. -/
theorem add (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .add destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .add destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left + right
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := result < left, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, MachineState.binary, valid, leftReadable, rightReadable, writable,
    BinaryOp.writes, BinaryOp.result, BinaryOp.carry, next, ExecutionStatus.advance,
    Bool.true_and, Bool.not_true, Bool.false_or, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, MachineState.writeOperand_status, location]
  rfl

theorem inc (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.inc register) := by decide +kernel) :
    let result := initial.registers register + 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (program.nextAddress address), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem dec (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.dec register) := by decide +kernel) :
    let result := initial.registers register - 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (program.nextAddress address), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem branch_zero (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .equal target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then target else program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, stepOp, Condition.holds]
  split <;> rfl

theorem branch_nonzero (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .notEqual target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then program.nextAddress address else target) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, stepOp, Condition.holds]
  cases initial.zeroFlag <;> rfl

theorem call (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (writable : permits initial.memory.writable (initial.registers .rsp - 8).toNat 8 = true := by rfl)
    (code : InstructionAt program address (.call target) := by decide +kernel) :
    Ensures program (· = initial) (· = {
      (initial.writeMemory (initial.registers .rsp - 8).toNat .qword
        (BitVec.ofNat 64 (program.nextAddress address))).write .rsp (initial.registers .rsp - 8) with
      status := .running target }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp]
  rw [ite_eq_left writable]

theorem return_ (program : Program) (address : Nat) (initial : MachineState)
    (location : initial.status = .running address) (slot : initial.ValidReturnSlot)
    (code : InstructionAt program address .ret := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write .rsp (initial.registers .rsp + 8) with
      status := .running initial.returnAddress, readHistory := initial.readHistory ++ [⟨(initial.registers .rsp).toNat,8⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [MachineState.write, MachineState.ValidReturnSlot, MachineState.returnAddress, stepOp]
theorem move (program : Program) (address : Nat) (destination source : Operand) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (valid : validMove destination source = true := by decide +kernel)
    (readable : initial.canRead source = true := by rfl)
    (writable : initial.canWrite destination = true := by rfl)
    (code : InstructionAt program address (.mov destination source) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.writeOperand destination (initial.readOperand source) with
      status := .running (program.nextAddress address), readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, next, ExecutionStatus.advance, location, valid, readable, writable]

theorem compare (program : Program) (address : Nat) (left right : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .cmp (.reg64 left) (.reg64 right)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address)
      zeroFlag := initial.registers left == initial.registers right,
      carryFlag := initial.registers left < initial.registers right,
      signFlag := (initial.registers left - initial.registers right).msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance]
  change (initial.registers left - initial.registers right == 0#64) =
    (initial.registers left == initial.registers right)
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem write_byte (program : Program) (address : Nat) (base : Reg) (source : Reg8) (initial : MachineState)
    (location : initial.status = .running address) (allowed : initial.memory.writable (initial.registers base).toNat = true)
    (code : InstructionAt program address (.mov (.memory .byte { base := some base }) (.reg8 source)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.writeMemory (initial.registers base).toNat .byte
      (((initial.registers source.parent).setWidth 8).setWidth 64) with
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have bound : (initial.registers base).toNat + 1 ≤ word := by
    have := (initial.registers base).isLt
    unfold word
    omega
  simp [stepOp, validMove, Operand.width, MachineState.canRead, MachineState.canWrite,
    MachineState.writeOperand, MachineState.readOperand, MachineState.recordRead,
    Address.evaluate, Scale.value,
    permits, next, ExecutionStatus.advance, allowed, bound]
  simp [MachineState.writeMemory, location]

theorem branch_below (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .below target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.carryFlag then target else program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, ExecutionStatus.advance, Condition.holds, location]
  split <;> rfl

end Rivet
