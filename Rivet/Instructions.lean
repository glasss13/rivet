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
/-- LEA computes an effective address from the initial registers. It neither
reads memory nor changes flags or read history. -/
theorem lea (program : Program) (address : Nat) (destination : Reg) (source : Address)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.lea destination source) := by first | assumption | decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination (source.evaluate initial.registers) with
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, next, ExecutionStatus.advance, MachineState.write, location]

/-- MOVZX zero-extends any modeled byte or word source into a 32-bit destination,
clearing its parent register's upper half and recording only actual memory reads. -/
theorem movzx (program : Program) (address : Nat) (destination : Reg32) (source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.movzx destination source) := by first | assumption | decide +kernel)
    (valid : source.width = some .byte ∨ source.width = some .word := by
      first | assumption | exact Or.inl rfl | exact Or.inr rfl)
    (readable : initial.canRead source = true := by first | assumption | simp) :
    Ensures program (· = initial) (· = { initial.write destination.parent (initial.readOperand source) with
      status := .running (program.nextAddress address)
      readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have encoded : (source.width == some .byte || source.width == some .word) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using valid
  simp [stepOp, encoded, readable, next, ExecutionStatus.advance, MachineState.write, location]

/-- MOVSXD sign-extends any modeled dword source to 64 bits. Flags are preserved;
memory sources require read permission and append their access to read history. -/
theorem movsxd (program : Program) (address : Nat) (destination : Reg) (source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.movsxd destination source) := by first | assumption | decide +kernel)
    (valid : source.width = some .dword := by first | assumption | rfl)
    (readable : initial.canRead source = true := by first | assumption | simp) :
    Ensures program (· = initial) (· = { initial.write destination ((initial.readOperand source).setWidth 32 |>.signExtend 64) with
      status := .running (program.nextAddress address)
      readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, valid, readable, next, ExecutionStatus.advance, MachineState.write, location]

-- Interpreter plumbing is shared privately; public rules expose opcode semantics.
private theorem binary (operation : BinaryOp) (program : Program) (address : Nat)
    (destination source : Operand) (initial : MachineState) (width : Width)
    (location : initial.status = .running address)
    (code : InstructionAt program address (.binary operation destination source))
    (hasWidth : destination.width = some width)
    (valid : validBinary operation destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : (!operation.writes || initial.canWrite destination) = true) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := operation.result left right initial.carryFlag
    let updated := if operation.writes then initial.writeOperand destination (result.setWidth 64) else initial
    Ensures program (· = initial) (· = { updated with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := operation.carry left right result initial.carryFlag, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, MachineState.binary, valid, leftReadable, rightReadable, writable,
    Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some]
  cases operation <;>
    simp [BinaryOp.writes, next, ExecutionStatus.advance, MachineState.writeOperand_status, location]

private theorem sub_beq_zero (left right : BitVec width) :
    (left - right == 0) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

/-- Successful ADD for every supported scalar width and operand form. -/
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
  exact binary .add program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

/-- Successful SUB for every supported scalar width and operand form. -/
theorem sub (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .sub destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .sub destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := left < right, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .sub program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

/-- Successful SBB for every supported scalar width and operand form. -/
theorem sbb (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .sbb destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .sbb destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right - (if initial.carryFlag then 1 else 0)
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := left < right || (initial.carryFlag && left == right), signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .sbb program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

/-- Successful CMP for every supported scalar width and operand form. Reads both operands without requiring write permission. -/
theorem compare (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .cmp destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .cmp destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address), zeroFlag := left == right,
      carryFlag := left < right, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  simpa only [BinaryOp.writes, Bool.false_eq_true, ite_false, BinaryOp.result, BinaryOp.carry, sub_beq_zero] using
    binary .cmp program address destination source initial width location code hasWidth valid
      leftReadable rightReadable (by rfl)

/-- Successful TEST for every supported scalar width and operand form. Reads both operands without requiring write permission. -/
theorem test (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .test destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .test destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left &&& right
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .test program address destination source initial width location code hasWidth valid
      leftReadable rightReadable (by rfl)

/-- Successful AND for every supported scalar width and operand form. -/
theorem bitwise_and (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .and destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .and destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left &&& right
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .and program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

/-- Successful OR for every supported scalar width and operand form. -/
theorem bitwise_or (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .or destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .or destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left ||| right
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .or program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

/-- Successful XOR for every supported scalar width and operand form. -/
theorem bitwise_xor (program : Program) (address : Nat) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.binary .xor destination source) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .xor destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead destination = true := by simp)
    (rightReadable : initial.canRead source = true := by simp)
    (writable : initial.canWrite destination = true := by simp) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left ^^^ right
    Ensures program (· = initial) (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (program.nextAddress address), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb
      readHistory := ((initial.recordRead destination).recordRead source).readHistory }) := by
  exact binary .xor program address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

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

/-- NOP preserves the entire state except for advancing the program counter. -/
theorem nop (program : Program) (address : Nat) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address .nop := by first | assumption | decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, next, ExecutionStatus.advance, location]

/-- JMP preserves the entire state except for setting the program counter. -/
theorem jump (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.jmp target) := by first | assumption | decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running target }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  rfl

/-- Jcc tests the initial flags, branching or falling through without changing
registers, flags, memory, or read history. Covers every modeled condition. -/
theorem branch (program : Program) (address : Nat) (condition : Condition) (target : Nat)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.jcc condition target) := by first | assumption | decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (if condition.holds initial then target else program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, ExecutionStatus.advance, location]
  split <;> rfl

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

end Rivet
