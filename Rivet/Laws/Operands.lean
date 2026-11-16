module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.SimpSet
import all Rivet.Interpreter.Machine
import all Rivet.Interpreter.Memory
-- Laws of the closed operand checks, operand values, and address evaluation: the `rivet` simp set.
@[expose] public section
namespace Rivet

@[rivet] theorem MachineState.canRead_reg8 (state : MachineState) (image : Image) (register : Reg8) :
    state.canRead image (.reg8 register) = true := by simp [canRead]
@[rivet] theorem MachineState.canRead_reg16 (state : MachineState) (image : Image) (register : Reg16) :
    state.canRead image (.reg16 register) = true := by simp [canRead]
@[rivet] theorem MachineState.canRead_reg32 (state : MachineState) (image : Image) (register : Reg32) :
    state.canRead image (.reg32 register) = true := by simp [canRead]
@[rivet] theorem MachineState.canRead_reg64 (state : MachineState) (image : Image) (register : Reg) :
    state.canRead image (.reg64 register) = true := by simp [canRead]
@[rivet] theorem MachineState.canRead_immediate (state : MachineState) (image : Image) (value : Int) :
    state.canRead image (.immediate value) = true := by simp [canRead]
@[rivet] theorem MachineState.canRead_memory (state : MachineState) (image : Image) (width : Width)
    (address : Address) :
    state.canRead image (.memory width address) = permits image.readable (address.evaluate state.registers)
      width.bytes := by simp [canRead]

@[rivet] theorem MachineState.canWrite_reg8 (state : MachineState) (image : Image) (register : Reg8) :
    state.canWrite image (.reg8 register) = true := by simp [canWrite]
@[rivet] theorem MachineState.canWrite_reg16 (state : MachineState) (image : Image) (register : Reg16) :
    state.canWrite image (.reg16 register) = true := by simp [canWrite]
@[rivet] theorem MachineState.canWrite_reg32 (state : MachineState) (image : Image) (register : Reg32) :
    state.canWrite image (.reg32 register) = true := by simp [canWrite]
@[rivet] theorem MachineState.canWrite_reg64 (state : MachineState) (image : Image) (register : Reg) :
    state.canWrite image (.reg64 register) = true := by simp [canWrite]
@[rivet] theorem MachineState.canWrite_immediate (state : MachineState) (image : Image) (value : Int) :
    state.canWrite image (.immediate value) = false := by simp [canWrite]
@[rivet] theorem MachineState.canWrite_memory (state : MachineState) (image : Image) (width : Width)
    (address : Address) :
    state.canWrite image (.memory width address) = permits image.writable (address.evaluate state.registers)
      width.bytes := by simp [canWrite]

@[rivet] theorem MachineState.readOperand_reg8 (state : MachineState) (register : Reg8) :
    state.readOperand .byte (.reg8 register) = (state.registers register.parent).setWidth 8 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_reg16 (state : MachineState) (register : Reg16) :
    state.readOperand .word (.reg16 register) = (state.registers register.parent).setWidth 16 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_reg32 (state : MachineState) (register : Reg32) :
    state.readOperand .dword (.reg32 register) = (state.registers register.parent).setWidth 32 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_reg64 (state : MachineState) (register : Reg) :
    state.readOperand .qword (.reg64 register) = state.registers register := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_byte (state : MachineState) (address : Address) :
    state.readOperand .byte (.memory .byte address) = readBytes state.memory (address.evaluate state.registers) 1 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_word (state : MachineState) (address : Address) :
    state.readOperand .word (.memory .word address) = readBytes state.memory (address.evaluate state.registers) 2 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_dword (state : MachineState) (address : Address) :
    state.readOperand .dword (.memory .dword address) = readBytes state.memory (address.evaluate state.registers) 4 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_qword (state : MachineState) (address : Address) :
    state.readOperand .qword (.memory .qword address) = readBytes state.memory (address.evaluate state.registers) 8 := by
  simp [readOperand, readOperand64]
@[rivet] theorem MachineState.readOperand_immediate (state : MachineState) (width : Width) (value : Int) :
    state.readOperand width (.immediate value) = BitVec.ofInt width.bits value := by
  apply BitVec.eq_of_toNat_eq
  cases width <;> simp [readOperand, readOperand64, BitVec.toNat_ofInt] <;> omega

@[rivet] theorem MachineState.writeOperand_reg8 (state : MachineState) (register : Reg8) (value : BitVec 8) :
    state.writeOperand .byte (.reg8 register) value = state.write register.parent
      ((state.registers register.parent &&& ~~~(255#64)) ||| value.setWidth 64) := by
  simp [writeOperand, writeOperand64]
@[rivet] theorem MachineState.writeOperand_reg16 (state : MachineState) (register : Reg16) (value : BitVec 16) :
    state.writeOperand .word (.reg16 register) value = state.write register.parent
      ((state.registers register.parent &&& ~~~(65535#64)) ||| value.setWidth 64) := by
  simp [writeOperand, writeOperand64]
@[rivet] theorem MachineState.writeOperand_reg32 (state : MachineState) (register : Reg32) (value : BitVec 32) :
    state.writeOperand .dword (.reg32 register) value = state.write register.parent (value.setWidth 64) := by
  simp [writeOperand, writeOperand64]
@[rivet] theorem MachineState.writeOperand_reg64 (state : MachineState) (register : Reg) (value : BitVec 64) :
    state.writeOperand .qword (.reg64 register) value = state.write register value := by
  simp [writeOperand, writeOperand64]
@[rivet] theorem MachineState.writeOperand_memory (state : MachineState) (width : Width) (address : Address)
    (value : BitVec width.bits) :
    state.writeOperand width (.memory width address) value =
      state.writeMemory (address.evaluate state.registers) width value := by
  have same : littleEndianAt (value.setWidth 64) (address.evaluate state.registers) =
      littleEndianAt value (address.evaluate state.registers) := by
    have fits : value.toNat < 2^64 := Nat.lt_of_lt_of_le value.isLt (by cases width <;> decide)
    unfold littleEndianAt
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits]
  simp only [writeOperand, writeOperand64, MachineState.writeMemory, same]
@[rivet] theorem MachineState.writeOperand_immediate (state : MachineState) (width : Width) (operand : Int)
    (value : BitVec width.bits) :
    state.writeOperand width (.immediate operand) value = state := by
  simp [writeOperand, writeOperand64]

-- Register aliases name their parent: `Reg32.edx.parent` is `.rdx`. Syntax only, so
-- these stay open; they are in the `rivet` set but not the default simp set.
attribute [rivet] Reg8.parent Reg16.parent Reg32.parent

@[rivet] theorem Address.evaluate_base (base : Reg) (scale : Scale) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := some base, index := none, scale, displacement } registers =
      registers base + BitVec.ofInt 64 displacement := by
  simp [evaluate]

@[rivet] theorem Address.evaluate_base_index_one (base index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := some base, index := some index, scale := .one, displacement } registers =
      registers base + registers index + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_base_index_two (base index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := some base, index := some index, scale := .two, displacement } registers =
      registers base + registers index * 2#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_base_index_four (base index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := some base, index := some index, scale := .four, displacement } registers =
      registers base + registers index * 4#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_base_index_eight (base index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := some base, index := some index, scale := .eight, displacement } registers =
      registers base + registers index * 8#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_index_one (index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := none, index := some index, scale := .one, displacement } registers =
      registers index + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_index_two (index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := none, index := some index, scale := .two, displacement } registers =
      registers index * 2#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_index_four (index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := none, index := some index, scale := .four, displacement } registers =
      registers index * 4#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_index_eight (index : Reg) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := none, index := some index, scale := .eight, displacement } registers =
      registers index * 8#64 + BitVec.ofInt 64 displacement := by
  simp [evaluate, Scale.value]

@[rivet] theorem Address.evaluate_absolute (scale : Scale) (displacement : Int)
    (registers : Reg → BitVec 64) :
    Address.evaluate { base := none, index := none, scale, displacement } registers =
      BitVec.ofInt 64 displacement := by
  simp [evaluate]

-- Access sizes as numbers of bytes.
attribute [rivet] Width.bytes

-- A condition as the flags it tests, and a status as its address.
attribute [rivet] Condition.holds ExecutionStatus.running.injEq

end Rivet
