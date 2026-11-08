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

@[simp] private theorem MachineState.writeOperand_status (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).status = state.status := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write, MachineState.writeMemory]

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
-- Private equalities connect the model's numeric encoding to lane/byte views.
private theorem append_nat (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2^n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

private theorem byte_extract (value : BitVec width) (offset : Nat) :
    (value.extractLsb' (8 * offset) 8).toFin =
      (⟨value.toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) := by
  apply Fin.ext
  change (value.extractLsb' (8 * offset) 8).toNat = _
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem shuffle_value (original : BitVec 128) (order : Nat) :
    BitVec.ofNat 128 ((List.range 4).foldr (fun lane result =>
      let selected := order / 4^lane % 4
      (original.toNat / 2^(32 * selected)) % 2^32 + 2^32 * result) 0) =
    (original.extractLsb' (32 * (order / 4^3 % 4)) 32 ++
     original.extractLsb' (32 * (order / 4^2 % 4)) 32 ++
     original.extractLsb' (32 * (order / 4^1 % 4)) 32 ++
     original.extractLsb' (32 * (order / 4^0 % 4)) 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [append_nat, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [List.range_succ, List.range_zero, List.foldr_append, List.foldr_cons, List.foldr_nil]
  have bound (lane : Nat) : (original.toNat / 2^(32 * (order / 4^lane % 4))) % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have b0 := bound 0
  have b1 := bound 1
  have b2 := bound 2
  have b3 := bound 3
  omega

/-- MOVD copies the initial low dword of a GPR into XMM and zeroes the upper
96 bits. Other XMM registers, GPRs, flags, memory, and history are preserved. -/
theorem movd (program : Program) (address : Nat) (destination : Xmm) (source : Reg32)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.movd destination source) := by first | assumption | decide +kernel) :
    let value := ((initial.registers source.parent).setWidth 32).setWidth 128
    Ensures program (· = initial) (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, next, ExecutionStatus.advance, location]

/-- PSHUFD selects four initial dword lanes with the immediate's four two-bit
selectors. Lane 0 is least significant; source/destination aliasing is allowed. -/
theorem pshufd (program : Program) (address : Nat) (destination source : Xmm) (order : Nat)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.pshufd destination source order) := by first | assumption | decide +kernel)
    (encoded : order < 256 := by first | assumption | omega) :
    let lane (index : Nat) : BitVec 32 :=
      (initial.xmmRegisters source).extractLsb' (32 * (order / 4^index % 4)) 32
    let value : BitVec 128 := lane 3 ++ lane 2 ++ lane 1 ++ lane 0
    Ensures program (· = initial) (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, encoded, ite_true]
  rw [shuffle_value]
  simp [next, ExecutionStatus.advance, location]

/-- An unaligned 128-bit load for either modeled XMM move kind. It records the
16-byte access and changes only the destination XMM register and fallthrough PC. -/
theorem load_xmm (program : Program) (address : Nat) (operation : XmmMove)
    (destination : Xmm) (source : Address) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.loadXmm operation destination source) := by first | assumption | decide +kernel)
    (readable : permits initial.memory.readable (source.evaluate initial.registers).toNat 16 = true := by
      first | assumption | rfl) :
    let pointer := (source.evaluate initial.registers).toNat
    let value := readBytes initial.memory pointer 16
    Ensures program (· = initial) (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (program.nextAddress address)
      readHistory := initial.readHistory ++ [⟨pointer,16⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, readable, next, ExecutionStatus.advance, location]

/-- An unaligned little-endian 128-bit store for either modeled XMM move kind.
Only write permission is required; registers, flags, and read history are preserved. -/
theorem store_xmm (program : Program) (address : Nat) (operation : XmmMove)
    (destination : Address) (source : Xmm) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.storeXmm operation destination source) := by first | assumption | decide +kernel)
    (writable : permits initial.memory.writable (destination.evaluate initial.registers).toNat 16 = true := by
      first | assumption | rfl) :
    let pointer := (destination.evaluate initial.registers).toNat
    Ensures program (· = initial) (· = { initial with
      memory := initial.memory.storeBytes pointer 16
        (fun offset => ((initial.xmmRegisters source).extractLsb' (8 * offset) 8).toFin)
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, writable, ite_true, next, ExecutionStatus.advance, location]
  simp only [byte_extract]

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

/-- Successful truncating signed IMUL for every modeled width and operand form.
The result and carry flag are specified; SF/ZF remain unconstrained for every
undefined-flag choice supply. Source reads always use the initial state. -/
theorem imul (program : Program) (address : Nat) (destination source : Operand)
    (immediate : Option Int) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.imul destination source immediate) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validImul destination source immediate = true := by
      first | assumption | (
        dsimp +instances [validImul, validConditionalMove, validBinary, validMove, Operand.width]
        all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
        all_goals omega))
    (readable : initial.canRead source = true := by first | assumption | simp) :
    let sourceValue := (initial.readOperand source).setWidth width.bits
    let multiplier : BitVec width.bits := match immediate with
      | none => (initial.readOperand destination).setWidth width.bits
      | some value => BitVec.ofInt width.bits value
    let product := sourceValue.toInt * multiplier.toInt
    let result := BitVec.ofInt width.bits product
    Ensures program (· = initial) (fun final => ∃ sign zero : Bool,
      final = { initial.writeOperand destination (result.setWidth 64) with
        status := .running (program.nextAddress address)
        carryFlag := result.toInt != product, signFlag := sign, zeroFlag := zero
        readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  refine ⟨undefinedFlags.signFlag, undefinedFlags.zeroFlag, ?_⟩
  rw [one code location undefinedFlags]
  simp only [stepOp, valid, readable, Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, ExecutionStatus.advance, MachineState.writeOperand_status, location]
  cases immediate <;> rfl

/-- Successful SHL/SHR for supported immediate-count register forms. The
encoded count is masked to the operand width. Zero masked counts preserve flags,
but still write the destination (and clear the upper half of an r32 parent). -/
theorem shift (program : Program) (address : Nat) (operation : ShiftOp)
    (destination : Operand) (count : Nat) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.shift operation destination count) := by first | assumption | decide +kernel)
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validShift destination count = true := by
      first | assumption | (simp [validShift] <;> omega)) :
    let amount := count % width.bits
    let value := (initial.readOperand destination).setWidth width.bits
    let result : BitVec width.bits := match operation with
      | .shl => BitVec.shiftLeft value amount
      | .shr => BitVec.ushiftRight value amount
    let updated := initial.writeOperand destination (result.setWidth 64)
    Ensures program (· = initial) (· = if amount == 0 then
      { updated with status := .running (program.nextAddress address) }
    else { updated with
      status := .running (program.nextAddress address)
      carryFlag := value.getLsbD (match operation with | .shl => width.bits - amount | .shr => amount - 1)
      zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have zero (value : BitVec width.bits) : (value.toNat == 0) = (value == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equal; exact BitVec.eq_of_toNat_eq equal
    · intro equal; rw [equal]; rfl
  simp only [stepOp, valid, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some]
  cases operation <;> split <;>
    simp only [zero] <;> simp_all [next, ExecutionStatus.advance]

/-- NOT complements a supported register or memory destination without changing
flags; memory destinations require read/write permission and record the read. -/
theorem bitwise_not (program : Program) (address : Nat) (destination : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.not destination) := by first | assumption | decide +kernel)
    (readable : initial.canRead destination = true := by first | assumption | simp)
    (writable : initial.canWrite destination = true := by first | assumption | simp) :
    Ensures program (· = initial) (· = { initial.writeOperand destination (~~~(initial.readOperand destination)) with
      status := .running (program.nextAddress address)
      readHistory := (initial.recordRead destination).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, readable, writable, next, ExecutionStatus.advance, location]

/-- SETcc writes a byte containing zero or one according to the initial flags.
It requires only write access to its destination and performs no memory read. -/
theorem setcc (program : Program) (address : Nat) (condition : Condition) (destination : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.setcc condition destination) := by first | assumption | decide +kernel)
    (valid : destination.width = some .byte := by first | assumption | rfl)
    (writable : initial.canWrite destination = true := by first | assumption | simp) :
    Ensures program (· = initial) (· = { initial.writeOperand destination (if condition.holds initial then 1 else 0) with
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, valid, writable, next, ExecutionStatus.advance, location]

/-- CMOVcc reads its source even when not taken. Writing the selected value
through the destination preserves narrow-register semantics, including clearing
the upper half of a 32-bit destination on both paths. Flags are preserved. -/
theorem cmovcc (program : Program) (address : Nat) (condition : Condition) (destination source : Operand)
    (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.cmovcc condition destination source) := by first | assumption | decide +kernel)
    (valid : validConditionalMove destination source = true := by
      first | assumption | simp [validConditionalMove])
    (readable : initial.canRead source = true := by first | assumption | simp) :
    let value := if condition.holds initial then initial.readOperand source else initial.readOperand destination
    Ensures program (· = initial) (· = { initial.writeOperand destination value with
      status := .running (program.nextAddress address)
      readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, valid, readable, next, ExecutionStatus.advance, location]

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

/-- PUSH stores the source's initial 64-bit value before updating RSP. Only
write permission for the eight-byte slot at the decremented pointer is required. -/
theorem push (program : Program) (address : Nat) (source : Reg) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.push source) := by first | assumption | decide +kernel)
    (writable : permits initial.memory.writable (initial.registers .rsp - 8).toNat 8 = true := by
      first | assumption | rfl) :
    Ensures program (· = initial) (· = {
      (initial.writeMemory (initial.registers .rsp - 8).toNat .qword (initial.registers source)).write
        .rsp (initial.registers .rsp - 8) with status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp, writable, ite_true]
  simp [next, MachineState.write, MachineState.writeMemory, ExecutionStatus.advance, location]

/-- POP reads the old stack slot, increments RSP, then writes the destination.
For POP RSP the loaded value replaces the incremented pointer. Flags and memory
are preserved, and the eight-byte read is recorded at the original pointer. -/
theorem pop (program : Program) (address : Nat) (destination : Reg) (initial : MachineState)
    (location : initial.status = .running address := by first | assumption | rfl)
    (code : InstructionAt program address (.pop destination) := by first | assumption | decide +kernel)
    (readable : permits initial.memory.readable (initial.registers .rsp).toNat 8 = true := by
      first | assumption | rfl) :
    Ensures program (· = initial) (· = {
      (initial.write .rsp (initial.registers .rsp + 8)).write destination
        (readBytes initial.memory (initial.registers .rsp).toNat 8) with
      status := .running (program.nextAddress address)
      readHistory := initial.readHistory ++ [⟨(initial.registers .rsp).toNat,8⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, readable, next, MachineState.write, ExecutionStatus.advance, location]

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
