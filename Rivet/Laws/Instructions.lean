module
public import Rivet.Laws.Ensures
public import Rivet.Laws.Operands
import all Rivet.Interpreter.Machine
import all Rivet.Laws.Ensures
-- Instruction contracts: one `Ensures` rule per modeled operation, proved against `step`.
@[expose] public section
namespace Rivet

-- Normalize known operand constructors without expanding unknown operands.
-- These equations already exist; only their simplification attributes are new.
-- Permission checks and operand reads and writes are closed; their equations are
-- in `Rivet.Laws.Operands`.
attribute [simp] Operand.width.eq_1 Operand.width.eq_2 Operand.width.eq_3
  Operand.width.eq_4 Operand.width.eq_5 Operand.width.eq_6

@[simp] private theorem MachineState.writeOperand_status (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).status = state.status := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write, MachineState.writeMemory]

private theorem MachineState.writeOperand_flags (state : MachineState) (operand : Operand)
    (value : BitVec 64) :
    (state.writeOperand operand value).carryFlag = state.carryFlag ∧
      (state.writeOperand operand value).zeroFlag = state.zeroFlag ∧
      (state.writeOperand operand value).signFlag = state.signFlag := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write, MachineState.writeMemory]

private theorem one (code : InstructionAt image.program address length instruction)
    (location : initial.status = .running address) (undefinedFlags : FlagValues) :
    step image initial undefinedFlags = stepOp image instruction (address + BitVec.ofNat 64 length) initial undefinedFlags := by
  simp only [step, location, code]

-- Every instruction has the same contract shape as a multi-instruction block.
-- `code` is always supplied: by `rivet_fetch` for concrete programs, or a hypothesis.
-- Private equalities connect the model's numeric encoding to lane/byte views.
private theorem append_nat (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2^n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

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

theorem movd (image : Image) (address : BitVec 64) (destination : Xmm) (source : Reg32)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.movd destination source)) :
    let value := ((initial.registers source.parent).setWidth 32).setWidth 128
    Ensures image initial (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, next, location]

theorem pshufd (image : Image) (address : BitVec 64) (destination source : Xmm) (order : Nat)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.pshufd destination source order))
    (encoded : order < 256 := by first | assumption | omega) :
    let lane (index : Nat) : BitVec 32 :=
      (initial.xmmRegisters source).extractLsb' (32 * (order / 4^index % 4)) 32
    let value : BitVec 128 := lane 3 ++ lane 2 ++ lane 1 ++ lane 0
    Ensures image initial (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp, encoded, ite_true]
  rw [shuffle_value]
  simp [next, location]

theorem load_xmm (image : Image) (address : BitVec 64) (operation : XmmMove)
    (destination : Xmm) (source : Address) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.loadXmm operation destination source))
    (readable : permits image.readable (source.evaluate initial.registers) 16#64 = true :=
      by simp only [rivet, *]) :
    let pointer := source.evaluate initial.registers
    let value := readBytes initial.memory pointer 16
    Ensures image initial (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, readable, next, location]

theorem store_xmm (image : Image) (address : BitVec 64) (operation : XmmMove)
    (destination : Address) (source : Xmm) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.storeXmm operation destination source))
    (writable : permits image.writable (destination.evaluate initial.registers) 16#64 = true :=
      by simp only [rivet, *]) :
    let pointer := destination.evaluate initial.registers
    Ensures image initial (· = { initial with
      memory := initial.memory.storeBytes pointer 16#64 (littleEndianAt (initial.xmmRegisters source) pointer)
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp, writable, ite_true, next, location]

theorem lea (image : Image) (address : BitVec 64) (destination : Reg) (source : Address)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.lea destination source)) :
    Ensures image initial (· = { initial.write destination (source.evaluate initial.registers) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, next, MachineState.write, location]

theorem movzx (image : Image) (address : BitVec 64) (destination : Reg32) (source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.movzx destination source))
    (valid : source.width = some .byte ∨ source.width = some .word := by
      first | assumption | exact Or.inl rfl | exact Or.inr rfl)
    (readable : initial.canRead image source = true := by simp only [rivet, *]) :
    Ensures image initial (· = { initial.write destination.parent (initial.readOperand source) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  have encoded : (source.width == some .byte || source.width == some .word) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using valid
  simp [stepOp, encoded, readable, next, MachineState.write, location]

theorem movsxd (image : Image) (address : BitVec 64) (destination : Reg) (source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.movsxd destination source))
    (valid : source.width = some .dword := by first | rfl | assumption)
    (readable : initial.canRead image source = true := by simp only [rivet, *]) :
    Ensures image initial (· = { initial.write destination ((initial.readOperand source).setWidth 32 |>.signExtend 64) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, valid, readable, next, MachineState.write, location]

-- Interpreter plumbing is shared privately; public rules expose opcode semantics.
private theorem binary (operation : BinaryOp) (image : Image) (address : BitVec 64)
    (destination source : Operand) (initial : MachineState) (width : Width)
    {length : Nat}
    (location : initial.status = .running address)
    (code : InstructionAt image.program address length (.binary operation destination source))
    (hasWidth : destination.width = some width)
    (valid : validBinary operation destination source = true)
    (leftReadable : initial.canRead image destination = true)
    (rightReadable : initial.canRead image source = true)
    (writable : (!operation.writes || initial.canWrite image destination) = true) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := operation.result left right initial.carryFlag
    let updated := if operation.writes then initial.writeOperand destination (result.setWidth 64) else initial
    Ensures image initial (· = { updated with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := operation.carry left right result initial.carryFlag, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp, MachineState.binary, valid, leftReadable, rightReadable, writable,
    Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some]
  cases operation <;>
    simp [BinaryOp.writes, next, MachineState.writeOperand_status, location]

private theorem sub_beq_zero (left right : BitVec width) :
    (left - right == 0) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem add (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .add destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .add destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left + right
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := result < left, signFlag := result.msb }) := by
  exact binary .add image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem sub (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .sub destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .sub destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := left < right, signFlag := result.msb }) := by
  exact binary .sub image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem sbb (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .sbb destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .sbb destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right - (if initial.carryFlag then 1 else 0)
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := left < right || (initial.carryFlag && left == right), signFlag := result.msb }) := by
  exact binary .sbb image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem compare (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .cmp destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .cmp destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left - right
    Ensures image initial (· = { initial with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := left == right,
      carryFlag := left < right, signFlag := result.msb }) := by
  simpa only [BinaryOp.writes, Bool.false_eq_true, ite_false, BinaryOp.result, BinaryOp.carry, sub_beq_zero] using
    binary .cmp image address destination source initial width location code hasWidth valid
      leftReadable rightReadable (by rfl)

theorem test (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .test destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .test destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left &&& right
    Ensures image initial (· = { initial with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb }) := by
  exact binary .test image address destination source initial width location code hasWidth valid
      leftReadable rightReadable (by rfl)

theorem bitwise_and (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .and destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .and destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left &&& right
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb }) := by
  exact binary .and image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem bitwise_or (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .or destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .or destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left ||| right
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb }) := by
  exact binary .or image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem bitwise_xor (image : Image) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.binary .xor destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validBinary .xor destination source = true := by
      dsimp +instances [validBinary, validMove, Operand.width]
      all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
      all_goals omega)
    (leftReadable : initial.canRead image destination = true := by simp only [rivet, *])
    (rightReadable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    let left := (initial.readOperand destination).setWidth width.bits
    let right := (initial.readOperand source).setWidth width.bits
    let result := left ^^^ right
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0,
      carryFlag := false, signFlag := result.msb }) := by
  exact binary .xor image address destination source initial width location code hasWidth valid
      leftReadable rightReadable writable

theorem imul (image : Image) (address : BitVec 64) (destination source : Operand)
    (immediate : Option Int) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.imul destination source immediate))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width := by rfl)
    (valid : validImul destination source immediate = true := by
      first | assumption | (
        dsimp +instances [validImul, validConditionalMove, validBinary, validMove, Operand.width]
        all_goals simp_all +instances [Bool.and_eq_true, decide_eq_true_eq]
        all_goals omega))
    (readable : initial.canRead image source = true := by simp only [rivet, *]) :
    let sourceValue := (initial.readOperand source).setWidth width.bits
    let multiplier : BitVec width.bits := match immediate with
      | none => (initial.readOperand destination).setWidth width.bits
      | some value => BitVec.ofInt width.bits value
    let product := sourceValue.toInt * multiplier.toInt
    let result := BitVec.ofInt width.bits product
    Ensures image initial (fun final => ∃ sign zero : Bool,
      final = { initial.writeOperand destination (result.setWidth 64) with
        status := .running (address + BitVec.ofNat 64 length)
        carryFlag := result.toInt != product, signFlag := sign, zeroFlag := zero }) := by
  apply Ensures.of_step
  intro undefinedFlags
  refine ⟨undefinedFlags.signFlag, undefinedFlags.zeroFlag, ?_⟩
  rw [one code location undefinedFlags]
  simp only [stepOp, valid, readable, Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, MachineState.writeOperand_status, location]
  cases immediate <;> rfl

theorem shift (image : Image) (address : BitVec 64) (operation : ShiftOp)
    (destination : Operand) (count : Nat) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.shift operation destination count))
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
    Ensures image initial (· = { initial.writeOperand destination (result.setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length)
      carryFlag := if amount = 0 then initial.carryFlag else
        value.getLsbD (match operation with | .shl => width.bits - amount | .shr => amount - 1)
      zeroFlag := if amount = 0 then initial.zeroFlag else result == 0
      signFlag := if amount = 0 then initial.signFlag else result.msb }) := by
  apply Ensures.of_step
  intro undefinedFlags
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
    simp only [zero] <;> simp_all [next, MachineState.writeOperand_flags]

theorem bitwise_not (image : Image) (address : BitVec 64) (destination : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.not destination))
    (readable : initial.canRead image destination = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    Ensures image initial (· = { initial.writeOperand destination (~~~(initial.readOperand destination)) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, readable, writable, next, location]

theorem setcc (image : Image) (address : BitVec 64) (condition : Condition) (destination : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.setcc condition destination))
    (valid : destination.width = some .byte := by first | rfl | assumption)
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    Ensures image initial (· = { initial.writeOperand destination (if condition.holds initial then 1 else 0) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, valid, writable, next, location]

theorem cmovcc (image : Image) (address : BitVec 64) (condition : Condition) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.cmovcc condition destination source))
    (valid : validConditionalMove destination source = true := by
      first | assumption | simp [validConditionalMove])
    (readable : initial.canRead image source = true := by simp only [rivet, *]) :
    let value := if condition.holds initial then initial.readOperand source else initial.readOperand destination
    Ensures image initial (· = { initial.writeOperand destination value with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, valid, readable, next, location]

theorem inc (image : Image) (address : BitVec 64) (register : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.inc register)) :
    let result := initial.registers register + 1
    Ensures image initial (· = { initial.write register result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp_all [MachineState.write, stepOp, next] <;> try rfl

theorem dec (image : Image) (address : BitVec 64) (register : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.dec register)) :
    let result := initial.registers register - 1
    Ensures image initial (· = { initial.write register result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp_all [MachineState.write, stepOp, next] <;> try rfl

theorem nop (image : Image) (address : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length .nop) :
    Ensures image initial (· = { initial with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, next, location]

theorem jump (image : Image) (address target : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.jmp target)) :
    Ensures image initial (· = { initial with status := .running target }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  rfl

theorem branch (image : Image) (address : BitVec 64) (condition : Condition) (target : BitVec 64)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.jcc condition target)) :
    Ensures image initial (· = { initial with
      status := .running (if condition.holds initial then target else (address + BitVec.ofNat 64 length)) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp, next, location]
  split <;> rfl

theorem push (image : Image) (address : BitVec 64) (source : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.push source))
    (writable : permits image.writable (initial.registers .rsp - 8#64) 8#64 = true :=
      by simp only [rivet, *]) :
    Ensures image initial (· = {
      (initial.writeMemory (initial.registers .rsp - 8#64) .qword (initial.registers source)).write
        .rsp (initial.registers .rsp - 8#64) with status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp, writable, ite_true]
  simp [next, MachineState.write, MachineState.writeMemory, location]

theorem pop (image : Image) (address : BitVec 64) (destination : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.pop destination))
    (readable : permits image.readable (initial.registers .rsp) 8#64 = true :=
      by simp only [rivet, *]) :
    Ensures image initial (· = {
      (initial.write .rsp (initial.registers .rsp + 8#64)).write destination
        (readBytes initial.memory (initial.registers .rsp) 8) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, readable, next, MachineState.write, location]

theorem call (image : Image) (address target : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.call target))
    (writable : permits image.writable (initial.registers .rsp - 8#64) 8#64 = true :=
      by simp only [rivet, *]) :
    Ensures image initial (· = {
      (initial.writeMemory (initial.registers .rsp - 8#64) .qword
        (address + BitVec.ofNat 64 length)).write .rsp (initial.registers .rsp - 8#64) with
      status := .running target }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp only [stepOp]
  rw [ite_eq_left writable]

theorem return_ (image : Image) (address : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length .ret)
    (readable : permits image.readable (initial.registers .rsp) 8#64 = true :=
      by simp only [rivet, *]) :
    Ensures image initial (· = { initial.write .rsp (initial.registers .rsp + 8#64) with
      status := .running (readBytes initial.memory (initial.registers .rsp) 8) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp_all [MachineState.write, stepOp]
theorem move (image : Image) (address : BitVec 64) (destination source : Operand) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address := by first | rfl | assumption)
    (code : InstructionAt image.program address length (.mov destination source))
    (valid : validMove destination source = true := by decide +kernel)
    (readable : initial.canRead image source = true := by simp only [rivet, *])
    (writable : initial.canWrite image destination = true := by simp only [rivet, *]) :
    Ensures image initial (· = { initial.writeOperand destination (initial.readOperand source) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Ensures.of_step
  intro undefinedFlags
  rw [one code location undefinedFlags]
  simp [stepOp, next, location, valid, readable, writable]

end Rivet
