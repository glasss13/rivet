module
public import Rivet.Laws.Block
public import Rivet.Laws.Operands
import all Rivet.Interpreter.Machine
import all Rivet.Interpreter.Memory
import all Rivet.Laws.Block
-- Instruction contracts: one `Block` per modeled operation, proved against `step`. The contract for
-- `Op.x` is `Contract.x`; for `Op.binary .y`, it is `Contract.y`; for `Op.syscall`, it is the system
-- call's, `Contract.exitGroup`.
@[expose] public section
namespace Rivet

private theorem MachineState.writeOperand64_flags (state : MachineState) (operand : Operand)
    (value : BitVec 64) :
    (state.writeOperand64 operand value).carryFlag = state.carryFlag ∧
      (state.writeOperand64 operand value).zeroFlag = state.zeroFlag ∧
      (state.writeOperand64 operand value).signFlag = state.signFlag ∧
      (state.writeOperand64 operand value).overflowFlag = state.overflowFlag := by
  cases operand <;> simp [MachineState.writeOperand64, MachineState.write, MachineState.writeMemory]

-- A store of the instruction's width keeps only that many low bytes of the value.
private theorem MachineState.writeOperand64_setWidth (state : MachineState) (operand : Operand)
    (value : BitVec 64) (hasWidth : operand.width = some width) :
    state.writeOperand64 operand ((value.setWidth width.bits).setWidth 64) = state.writeOperand64 operand value := by
  cases operand <;> simp only [Operand.width, Option.some.injEq, reduceCtorEq] at hasWidth <;> subst hasWidth
  case memory width address =>
    simp only [MachineState.writeOperand64, MachineState.writeMemory, MachineState.mk.injEq, and_true,
      true_and]
    funext other
    simp only [Memory.storeBytes]
    split
    · next inside =>
      have offset : (other - address.evaluate state.registers).toNat < width.bytes := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside.1)]
        omega
      have bits : 2 ^ width.bits = 256 ^ width.bytes := by cases width <;> rfl
      have fits : value.toNat % 256 ^ width.bytes < 2 ^ 64 :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by decide))) (by cases width <;> decide)
      unfold littleEndianAt
      apply Fin.ext
      simp only [BitVec.toNat_setWidth, bits]
      rw [Nat.mod_eq_of_lt fits]
      generalize (other - address.evaluate state.registers).toNat = byte at offset ⊢
      obtain ⟨rest, split⟩ : ∃ rest, width.bytes = byte + (rest + 1) := ⟨width.bytes - byte - 1, by omega⟩
      rw [split, Nat.pow_add, Nat.mod_mul_right_div_self, Nat.pow_succ, Nat.mod_mul_left_mod]
    · rfl
  all_goals simp [MachineState.writeOperand64]

private theorem one {initial : MachineState} (holds : initial.Holds code) (fetched : InstructionAt code address length instruction)
    (location : initial.status = .running address) (undefinedFlags : FlagValues) :
    step initial undefinedFlags = stepOp instruction (address + BitVec.ofNat 64 length) initial undefinedFlags := by
  simp only [step, location, holds.fetch fetched]

private theorem except_congr {t u s : MachineState} {c : Changes} (same : u.Except s c)
    (registers : t.registers = u.registers := by rfl) (xmm : t.xmmRegisters = u.xmmRegisters := by rfl)
    (memory : t.memory = u.memory := by rfl) (kernel : t.kernel = u.kernel := by rfl) :
    t.Except s c :=
  ⟨fun register out => registers ▸ same.sameRegisters register out,
    fun register out => xmm ▸ same.sameXmm register out,
    fun address size away fits => memory ▸ same.sameMemory address size away fits,
    fun out => kernel ▸ same.sameKernel out⟩

private theorem write_except (state : MachineState) (register : Reg) (value : BitVec 64) :
    (state.write register value).Except state { registers := [register] } :=
  ⟨fun other out => by simp_all [MachineState.write], fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩

private theorem write_write_except (state : MachineState) (first second : Reg) (one two : BitVec 64) :
    ((state.write first one).write second two).Except state { registers := [first, second] } :=
  ⟨fun other out => by simp_all [MachineState.write], fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩

private theorem store_except (state : MachineState) (base : BitVec 64) (length : Nat) (bytes : Memory) :
    ({ state with memory := state.memory.storeBytes base length bytes } : MachineState).Except state
      { memory := [(base.toNat, base.toNat + length)] } :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun address size away fits => Internal.readBytes_congr (fits := fits) fun other low high => by
    have := away _ List.mem_cons_self
    simp only [Memory.storeBytes]
    split <;> first | omega | rfl, fun _ => rfl⟩

private theorem writeXmm_except (state : MachineState) (destination : Xmm) (value : BitVec 128) :
    ({ state with xmmRegisters := fun register =>
        if register = destination then value else state.xmmRegisters register } : MachineState).Except state
      { xmm := [destination] } :=
  ⟨fun _ _ => rfl, fun other out => by simp_all, fun _ _ _ _ => rfl, fun _ => rfl⟩

private theorem push_except (state : MachineState) (value : BitVec 64) :
    ((state.writeMemory (state.registers .rsp - 8#64) .qword value).write .rsp
      (state.registers .rsp - 8#64)).Except state
      { registers := [.rsp], memory := [((state.registers .rsp - 8#64).toNat,
        (state.registers .rsp - 8#64).toNat + 8)] } :=
  ⟨fun other out => by simp_all [MachineState.write, MachineState.writeMemory], fun _ _ => rfl,
    fun address size away fits => Internal.readBytes_congr (fits := fits) fun other low high => by
    have := away _ List.mem_cons_self
    simp only [MachineState.write, MachineState.writeMemory, Memory.storeBytes, Width.bytes]
    split <;> first | omega | rfl, fun _ => rfl⟩

private theorem writeOperand_except (state : MachineState) (width : Width) (destination : Operand)
    (value : BitVec width.bits) :
    (state.writeOperand width destination value).Except state (destination.changes state) := by
  unfold MachineState.writeOperand MachineState.writeOperand64
  cases destination with
  | reg8 register | reg16 register | reg32 register | reg64 register => exact write_except _ _ _
  | memory width address => exact store_except _ _ _ _
  | immediate => exact Internal.MachineState.Except.refl

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

theorem Contract.movd (code : Code) (address : BitVec 64) (destination : Xmm) (source : Reg32)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.movd destination source)) :
    let value := ((initial.registers source.parent).setWidth 32).setWidth 128
    Block code initial { xmm := [destination] } (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeXmm_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, next]

theorem Contract.pshufd (code : Code) (address : BitVec 64) (destination source : Xmm) (order : Nat)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.pshufd destination source order))
    (encoded : order < 256) :
    let lane (index : Nat) : BitVec 32 :=
      (initial.xmmRegisters source).extractLsb' (32 * (order / 4^index % 4)) 32
    let value : BitVec 128 := lane 3 ++ lane 2 ++ lane 1 ++ lane 0
    Block code initial { xmm := [destination] } (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeXmm_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, encoded, ite_true]
  rw [shuffle_value]
  simp [next]

theorem Contract.loadXmm (code : Code) (address : BitVec 64) (operation : XmmMove)
    (destination : Xmm) (source : Address) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.loadXmm operation destination source))
    (readable : permits initial.kernel.readable (source.evaluate initial.registers) 16 = true) :
    let pointer := source.evaluate initial.registers
    let value := readBytes initial.memory pointer 16
    Block code initial { xmm := [destination] } (· = { initial with
      xmmRegisters := fun register => if register = destination then value else initial.xmmRegisters register
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeXmm_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, readable, next]

theorem Contract.storeXmm (code : Code) (address : BitVec 64) (operation : XmmMove)
    (destination : Address) (source : Xmm) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.storeXmm operation destination source))
    (writable : permits initial.kernel.writable (destination.evaluate initial.registers) 16 = true) :
    let pointer := destination.evaluate initial.registers
    Block code initial { memory := [(pointer.toNat, pointer.toNat + 16)] } (· = { initial with
      memory := initial.memory.storeBytes pointer 16 (littleEndianAt (initial.xmmRegisters source) pointer)
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (store_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, writable, ite_true, next]

theorem Contract.lea (code : Code) (address : BitVec 64) (destination : Operand) (source : Address)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.lea destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validLea destination = true) :
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination
        ((source.evaluate initial.registers).setWidth width.bits) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, next, valid, MachineState.writeOperand,
    MachineState.writeOperand64_setWidth initial destination _ hasWidth]

theorem Contract.movzx (code : Code) (address : BitVec 64) (destination : Reg32) (source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.movzx destination source))
    (width : Width := match source.width with
      | some width => width
      | none => .qword)
    (hasWidth : source.width = some width)
    (valid : width = .byte ∨ width = .word)
    (readable : initial.canRead source = true) :
    Block code initial { registers := [destination.parent] } (· = { initial.write destination.parent ((initial.readOperand width source).setWidth 64) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (write_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  have encoded : (source.width == some .byte || source.width == some .word) = true := by
    rcases valid with rfl | rfl <;> simp [hasWidth]
  have extended : ((initial.readOperand64 source).setWidth width.bits).setWidth 64 = initial.readOperand64 source := by
    rcases valid with rfl | rfl <;> cases source <;> simp_all [MachineState.readOperand64]
  simp [stepOp, encoded, readable, next, MachineState.write, MachineState.readOperand, extended]

private theorem signExtend_eq_add (value : BitVec 32) :
    value.signExtend 64 = value.setWidth 64 + if value < 0x80000000#32 then 0#64 else 0xFFFFFFFF00000000#64 := by
  apply BitVec.eq_of_toNat_eq
  have small := value.isLt
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_add]
  simp only [BitVec.lt_def]
  split <;> split <;> simp_all <;> omega

theorem Contract.movsxd (code : Code) (address : BitVec 64) (destination : Reg) (source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.movsxd destination source))
    (valid : source.width = some .dword)
    (readable : initial.canRead source = true) :
    let value := initial.readOperand .dword source
    Block code initial { registers := [destination] } (· = { initial.write destination
        (value.setWidth 64 + if value < 0x80000000#32 then 0#64 else 0xFFFFFFFF00000000#64) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  intro value
  rw [← signExtend_eq_add]
  apply Block.of_step (by rintro _ rfl; exact except_congr (write_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, valid, readable, next, MachineState.write, MachineState.readOperand, value]

-- Interpreter plumbing is shared privately; public rules expose opcode semantics.
private theorem binary (operation : BinaryOp) (code : Code) (address : BitVec 64)
    (destination source : Operand) (initial : MachineState) (width : Width)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary operation destination source))
    (hasWidth : destination.width = some width)
    (valid : validBinary operation destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : (!operation.writes || initial.canWrite destination) = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := operation.result left right initial.carryFlag
    let updated := if operation.writes then initial.writeOperand width destination result else initial
    Block code initial (if operation.writes then destination.changes initial else {}) (· = { updated with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := operation.carry left right result initial.carryFlag,
      overflowFlag := operation.overflow left right result initial.carryFlag, signFlag := result.msb }) := by
  apply Block.of_step (by rintro _ rfl; by_cases writes : operation.writes = true <;> simp only [writes, ↓reduceIte] <;>
    first | exact except_congr (writeOperand_except _ _ _ _) | exact except_congr Internal.MachineState.Except.refl)
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, MachineState.binary, valid, leftReadable, rightReadable, writable,
    Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, MachineState.readOperand, MachineState.writeOperand]
  cases operation <;>
    simp [BinaryOp.writes, next]

private theorem sub_beq_zero (left right : BitVec width) :
    (left - right == 0#width) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem Contract.add (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .add destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .add destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left + right
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := result < left, overflowFlag := left.saddOverflow right,
      signFlag := result.msb }) := by
  exact binary .add code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.sub (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .sub destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .sub destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left - right
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := left < right, overflowFlag := left.ssubOverflow right,
      signFlag := result.msb }) := by
  exact binary .sub code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.sbb (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .sbb destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .sbb destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left - right - (if initial.carryFlag then 1#width.bits else 0#width.bits)
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := left < right || (initial.carryFlag && left == right),
      overflowFlag := result.toInt != left.toInt - right.toInt - (if initial.carryFlag then 1 else 0),
      signFlag := result.msb }) := by
  exact binary .sbb code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.cmp (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .cmp destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .cmp destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left - right
    Block code initial {} (· = { initial with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := left == right,
      carryFlag := left < right, overflowFlag := left.ssubOverflow right,
      signFlag := result.msb }) := by
  simpa only [BinaryOp.writes, Bool.false_eq_true, ite_false, BinaryOp.result, BinaryOp.carry, BinaryOp.overflow,
    sub_beq_zero] using
    binary .cmp code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable (by rfl)

theorem Contract.test (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .test destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .test destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left &&& right
    Block code initial {} (· = { initial with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := false, overflowFlag := false, signFlag := result.msb }) := by
  exact binary .test code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable (by rfl)

theorem Contract.and (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .and destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .and destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left &&& right
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := false, overflowFlag := false, signFlag := result.msb }) := by
  exact binary .and code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.or (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .or destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .or destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left ||| right
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := false, overflowFlag := false, signFlag := result.msb }) := by
  exact binary .or code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.xor (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.binary .xor destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validBinary .xor destination source = true)
    (leftReadable : initial.canRead destination = true)
    (rightReadable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    let left := initial.readOperand width destination
    let right := initial.readOperand width source
    let result := left ^^^ right
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      carryFlag := false, overflowFlag := false, signFlag := result.msb }) := by
  exact binary .xor code address destination source initial width location fetched hasWidth valid
      leftReadable rightReadable writable

theorem Contract.imul (code : Code) (address : BitVec 64) (destination source : Operand)
    (immediate : Option Int) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.imul destination source immediate))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validImul destination source immediate = true)
    (readable : initial.canRead source = true) :
    let sourceValue := initial.readOperand width source
    let multiplier : BitVec width.bits := match immediate with
      | none => initial.readOperand width destination
      | some value => BitVec.ofInt width.bits value
    let product := sourceValue.toInt * multiplier.toInt
    let result := sourceValue * multiplier
    Block code initial (destination.changes initial) (fun final => ∃ sign zero : Bool,
      final = { initial.writeOperand width destination result with
        status := .running (address + BitVec.ofNat 64 length)
        carryFlag := result.toInt != product, overflowFlag := result.toInt != product,
        signFlag := sign, zeroFlag := zero }) := by
  apply Block.of_step (by rintro _ ⟨_, _, rfl⟩; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  refine ⟨undefinedFlags.signFlag, undefinedFlags.zeroFlag, ?_⟩
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, valid, readable, Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, MachineState.readOperand,
    MachineState.writeOperand]
  cases immediate <;> rfl

private theorem toNat_beq_zero (value : BitVec w) : (value.toNat == 0) = (value == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro equal; exact BitVec.eq_of_toNat_eq equal
  · intro equal; rw [equal]; rfl

theorem Contract.mul (code : Code) (address : BitVec 64) (source : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.mul source)) :
    let product := (initial.registers .rax).setWidth 128 * (initial.registers source).setWidth 128
    let high := (product >>> 64).setWidth 64
    Block code initial { registers := [.rax, .rdx] } (fun final => ∃ sign zero : Bool,
      final = { (initial.write .rax (initial.registers .rax * initial.registers source)).write .rdx high with
        status := .running (address + BitVec.ofNat 64 length)
        carryFlag := high != 0#64, overflowFlag := high != 0#64, signFlag := sign, zeroFlag := zero }) := by
  apply Block.of_step (by rintro _ ⟨_, _, rfl⟩; exact except_congr (write_write_except _ _ _ _ _))
  intro holds undefinedFlags
  refine ⟨undefinedFlags.signFlag, undefinedFlags.zeroFlag, ?_⟩
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, next, MachineState.write]

theorem Contract.tzcnt (code : Code) (address : BitVec 64) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.tzcnt destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validConditionalMove destination source = true)
    (readable : initial.canRead source = true) :
    let value := initial.readOperand width source
    let result := value.ctz
    Block code initial (destination.changes initial) (fun final => ∃ sign overflow : Bool,
      final = { initial.writeOperand width destination result with
        status := .running (address + BitVec.ofNat 64 length)
        carryFlag := value == 0#width.bits, zeroFlag := result == 0#width.bits,
        signFlag := sign, overflowFlag := overflow }) := by
  apply Block.of_step (by rintro _ ⟨_, _, rfl⟩; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  refine ⟨undefinedFlags.signFlag, undefinedFlags.overflowFlag, ?_⟩
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, valid, readable, Bool.true_and, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, MachineState.readOperand,
    MachineState.writeOperand, toNat_beq_zero]
  rfl

theorem Contract.shift (code : Code) (address : BitVec 64) (operation : ShiftOp)
    (destination : Operand) (count : Nat) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.shift operation destination count))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validShift destination count = true) :
    let amount := count % width.bits
    let value := initial.readOperand width destination
    let result : BitVec width.bits := match operation with
      | .shl => value <<< amount
      | .shr => value >>> amount
    Block code initial (destination.changes initial) (fun final => ∃ overflow : Bool,
      final = { initial.writeOperand width destination result with
        status := .running (address + BitVec.ofNat 64 length)
        carryFlag := if amount = 0 then initial.carryFlag else
          value.getLsbD (match operation with | .shl => width.bits - amount | .shr => amount - 1)
        zeroFlag := if amount = 0 then initial.zeroFlag else result == 0#width.bits
        signFlag := if amount = 0 then initial.signFlag else result.msb
        overflowFlag := if amount = 0 then initial.overflowFlag else if amount = 1 then
            (match operation with | .shl => result.msb != value.msb | .shr => value.msb)
          else overflow }) := by
  apply Block.of_step (by rintro _ ⟨_, rfl⟩; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  refine ⟨undefinedFlags.overflowFlag, ?_⟩
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, valid, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, MachineState.readOperand, MachineState.writeOperand]
  cases operation <;> split <;>
    simp only [toNat_beq_zero] <;> simp_all [next, MachineState.writeOperand64_flags]

theorem Contract.not (code : Code) (address : BitVec 64) (destination : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.not destination))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (readable : initial.canRead destination = true)
    (writable : initial.canWrite destination = true) :
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination (-initial.readOperand width destination - 1#width.bits) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  rw [← BitVec.not_eq_neg_add]
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  have narrow : width.bits ≤ 64 := by cases width <;> decide
  simp [stepOp, readable, writable, next, MachineState.readOperand, MachineState.writeOperand,
    ← BitVec.setWidth_not narrow, MachineState.writeOperand64_setWidth initial destination _ hasWidth]

theorem Contract.setcc (code : Code) (address : BitVec 64) (condition : Condition) (destination : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.setcc condition destination))
    (valid : destination.width = some .byte)
    (writable : initial.canWrite destination = true) :
    Block code initial (destination.changes initial) (· = { initial.writeOperand .byte destination (if condition.holds initial then 1#8 else 0#8) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  have narrowed : ((if condition.holds initial then 1 else 0 : BitVec 64).setWidth 8) =
      if condition.holds initial then 1#8 else 0#8 := by split <;> rfl
  simp only [stepOp, valid, writable, MachineState.writeOperand, ← narrowed,
    MachineState.writeOperand64_setWidth initial destination _ valid]
  simp [next]

theorem Contract.cmovcc (code : Code) (address : BitVec 64) (condition : Condition) (destination source : Operand)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.cmovcc condition destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validConditionalMove destination source = true)
    (readable : initial.canRead source = true) :
    let value := if condition.holds initial then initial.readOperand width source
      else initial.readOperand width destination
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination value with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, valid, readable, Bool.and_self, ite_true, MachineState.readOperand,
    MachineState.writeOperand, ← apply_ite (BitVec.setWidth width.bits),
    MachineState.writeOperand64_setWidth initial destination _ hasWidth]
  simp [next]

theorem Contract.inc (code : Code) (address : BitVec 64) (destination : Operand) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.inc destination))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (readable : initial.canRead destination = true)
    (writable : initial.canWrite destination = true) :
    let value := initial.readOperand width destination
    let result := value + 1#width.bits
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      signFlag := result.msb, overflowFlag := value.saddOverflow 1#width.bits }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, readable, writable, Bool.and_self, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, MachineState.readOperand,
    MachineState.writeOperand, toNat_beq_zero]
  rfl

theorem Contract.dec (code : Code) (address : BitVec 64) (destination : Operand) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.dec destination))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (readable : initial.canRead destination = true)
    (writable : initial.canWrite destination = true) :
    let value := initial.readOperand width destination
    let result := value - 1#width.bits
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination result with
      status := .running (address + BitVec.ofNat 64 length), zeroFlag := result == 0#width.bits,
      signFlag := result.msb, overflowFlag := value.ssubOverflow 1#width.bits }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, readable, writable, Bool.and_self, ite_true]
  rw [hasWidth]
  simp only [Option.getD_some, next, MachineState.readOperand,
    MachineState.writeOperand, toNat_beq_zero]
  rfl

theorem Contract.nop (code : Code) (address : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length .nop) :
    Block code initial {} (· = { initial with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr Internal.MachineState.Except.refl)
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, next]

theorem Contract.jmp (code : Code) (address target : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.jmp target)) :
    Block code initial {} (· = { initial with status := .running target }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr Internal.MachineState.Except.refl)
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  rfl

theorem Contract.jcc (code : Code) (address : BitVec 64) (condition : Condition) (target : BitVec 64)
    (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.jcc condition target)) :
    Block code initial {} (· = { initial with
      status := .running (if condition.holds initial then target else (address + BitVec.ofNat 64 length)) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr Internal.MachineState.Except.refl)
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, next]
  split <;> rfl

theorem Contract.push (code : Code) (address : BitVec 64) (source : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.push source))
    (writable : permits initial.kernel.writable (initial.registers .rsp - 8#64) 8 = true) :
    Block code initial { registers := [.rsp], memory := [((initial.registers .rsp - 8#64).toNat,
      (initial.registers .rsp - 8#64).toNat + 8)] } (· = {
      (initial.writeMemory (initial.registers .rsp - 8#64) .qword (initial.registers source)).write
        .rsp (initial.registers .rsp - 8#64) with status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (push_except _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp, writable, ite_true]
  simp [next, MachineState.write, MachineState.writeMemory]

theorem Contract.pop (code : Code) (address : BitVec 64) (destination : Reg) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.pop destination))
    (readable : permits initial.kernel.readable (initial.registers .rsp) 8 = true) :
    Block code initial { registers := [.rsp, destination] } (· = {
      (initial.write .rsp (initial.registers .rsp + 8#64)).write destination
        (readBytes initial.memory (initial.registers .rsp) 8) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (write_write_except _ _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, readable, next, MachineState.write]

theorem Contract.call (code : Code) (address target : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.call target))
    (writable : permits initial.kernel.writable (initial.registers .rsp - 8#64) 8 = true) :
    Block code initial { registers := [.rsp], memory := [((initial.registers .rsp - 8#64).toNat,
      (initial.registers .rsp - 8#64).toNat + 8)] } (· = {
      (initial.writeMemory (initial.registers .rsp - 8#64) .qword
        (address + BitVec.ofNat 64 length)).write .rsp (initial.registers .rsp - 8#64) with
      status := .running target }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (push_except _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp only [stepOp]
  rw [ite_eq_left writable]

theorem Contract.ret (code : Code) (address : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length .ret)
    (readable : permits initial.kernel.readable (initial.registers .rsp) 8 = true) :
    Block code initial { registers := [.rsp] } (· = { initial.write .rsp (initial.registers .rsp + 8#64) with
      status := .running (readBytes initial.memory (initial.registers .rsp) 8) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (write_except _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp_all [MachineState.write, stepOp]

theorem Contract.exitGroup (code : Code) (address : BitVec 64) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length .syscall)
    (number : initial.registers .rax = 231#64) :
    Block code initial {} (· = { initial with
      status := .exited ((initial.registers .rdi).setWidth 8) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr Internal.MachineState.Except.refl)
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, number]

theorem Contract.mov (code : Code) (address : BitVec 64) (destination source : Operand) (initial : MachineState)
    {length : Nat}
    (location : initial.status = .running address)
    (fetched : InstructionAt code address length (.mov destination source))
    (width : Width := match destination.width with
      | some width => width
      | none => .qword)
    (hasWidth : destination.width = some width)
    (valid : validMove destination source = true)
    (readable : initial.canRead source = true)
    (writable : initial.canWrite destination = true) :
    Block code initial (destination.changes initial) (· = { initial.writeOperand width destination (initial.readOperand width source) with
      status := .running (address + BitVec.ofNat 64 length) }) := by
  apply Block.of_step (by rintro _ rfl; exact except_congr (writeOperand_except _ _ _ _))
  intro holds undefinedFlags
  rw [one holds fetched location undefinedFlags]
  simp [stepOp, next, valid, readable, writable, MachineState.readOperand, MachineState.writeOperand,
    MachineState.writeOperand64_setWidth initial destination _ hasWidth]

end Rivet
