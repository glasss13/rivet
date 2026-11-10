module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.SimpSet
import all Rivet.Interpreter.Machine
-- Laws of the closed operand checks, operand values, and address evaluation: the `rivet` simp set.
@[expose] public section
namespace Rivet

/-! ## Permission checks

One equation per operand form. A memory operand needs `permits` over the bytes it
covers; registers always pass; an immediate cannot be written. These are in the
default simp set and the `rivet` set. -/

@[simp, rivet] theorem MachineState.canRead_reg8 (state : MachineState) (image : Image) (register : Reg8) :
    state.canRead image (.reg8 register) = true := by simp [canRead]
@[simp, rivet] theorem MachineState.canRead_reg16 (state : MachineState) (image : Image) (register : Reg16) :
    state.canRead image (.reg16 register) = true := by simp [canRead]
@[simp, rivet] theorem MachineState.canRead_reg32 (state : MachineState) (image : Image) (register : Reg32) :
    state.canRead image (.reg32 register) = true := by simp [canRead]
@[simp, rivet] theorem MachineState.canRead_reg64 (state : MachineState) (image : Image) (register : Reg) :
    state.canRead image (.reg64 register) = true := by simp [canRead]
@[simp, rivet] theorem MachineState.canRead_immediate (state : MachineState) (image : Image) (value : Int) :
    state.canRead image (.immediate value) = true := by simp [canRead]
@[simp, rivet] theorem MachineState.canRead_memory (state : MachineState) (image : Image) (width : Width)
    (address : Address) :
    state.canRead image (.memory width address) = permits image.readable (address.evaluate state.registers)
      (address.evaluate state.registers + BitVec.ofNat 64 width.bytes) := by simp [canRead]

@[simp, rivet] theorem MachineState.canWrite_reg8 (state : MachineState) (image : Image) (register : Reg8) :
    state.canWrite image (.reg8 register) = true := by simp [canWrite]
@[simp, rivet] theorem MachineState.canWrite_reg16 (state : MachineState) (image : Image) (register : Reg16) :
    state.canWrite image (.reg16 register) = true := by simp [canWrite]
@[simp, rivet] theorem MachineState.canWrite_reg32 (state : MachineState) (image : Image) (register : Reg32) :
    state.canWrite image (.reg32 register) = true := by simp [canWrite]
@[simp, rivet] theorem MachineState.canWrite_reg64 (state : MachineState) (image : Image) (register : Reg) :
    state.canWrite image (.reg64 register) = true := by simp [canWrite]
@[simp, rivet] theorem MachineState.canWrite_immediate (state : MachineState) (image : Image) (value : Int) :
    state.canWrite image (.immediate value) = false := by simp [canWrite]
@[simp, rivet] theorem MachineState.canWrite_memory (state : MachineState) (image : Image) (width : Width)
    (address : Address) :
    state.canWrite image (.memory width address) = permits image.writable (address.evaluate state.registers)
      (address.evaluate state.registers + BitVec.ofNat 64 width.bytes) := by simp [canWrite]

/-! ## Operand values

One equation per operand form for reading and writing. Narrow
registers read the low bits of their parent; a 32-bit write clears the upper half,
while 8- and 16-bit writes keep the remaining bits. In the default simp set and the
`rivet` set. -/

@[simp, rivet] theorem MachineState.readOperand_reg8 (state : MachineState) (register : Reg8) :
    state.readOperand (.reg8 register) = ((state.registers register.parent).setWidth 8).setWidth 64 := by
  simp [readOperand]
@[simp, rivet] theorem MachineState.readOperand_reg16 (state : MachineState) (register : Reg16) :
    state.readOperand (.reg16 register) = ((state.registers register.parent).setWidth 16).setWidth 64 := by
  simp [readOperand]
@[simp, rivet] theorem MachineState.readOperand_reg32 (state : MachineState) (register : Reg32) :
    state.readOperand (.reg32 register) = ((state.registers register.parent).setWidth 32).setWidth 64 := by
  simp [readOperand]
@[simp, rivet] theorem MachineState.readOperand_reg64 (state : MachineState) (register : Reg) :
    state.readOperand (.reg64 register) = state.registers register := by
  simp [readOperand]
@[simp, rivet] theorem MachineState.readOperand_memory (state : MachineState) (width : Width) (address : Address) :
    state.readOperand (.memory width address) =
      (readBytes state.memory (address.evaluate state.registers) width.bytes).setWidth 64 := by
  simp [readOperand]
@[simp, rivet] theorem MachineState.readOperand_immediate (state : MachineState) (value : Int) :
    state.readOperand (.immediate value) = BitVec.ofInt 64 value := by
  simp [readOperand]

@[simp, rivet] theorem MachineState.writeOperand_reg8 (state : MachineState) (register : Reg8) (value : BitVec 64) :
    state.writeOperand (.reg8 register) value = state.write register.parent
      ((state.registers register.parent &&& ~~~(255#64)) ||| ((value.setWidth 8).setWidth 64)) := by
  simp [writeOperand]
@[simp, rivet] theorem MachineState.writeOperand_reg16 (state : MachineState) (register : Reg16) (value : BitVec 64) :
    state.writeOperand (.reg16 register) value = state.write register.parent
      ((state.registers register.parent &&& ~~~(65535#64)) ||| ((value.setWidth 16).setWidth 64)) := by
  simp [writeOperand]
@[simp, rivet] theorem MachineState.writeOperand_reg32 (state : MachineState) (register : Reg32) (value : BitVec 64) :
    state.writeOperand (.reg32 register) value = state.write register.parent ((value.setWidth 32).setWidth 64) := by
  simp [writeOperand]
@[simp, rivet] theorem MachineState.writeOperand_reg64 (state : MachineState) (register : Reg) (value : BitVec 64) :
    state.writeOperand (.reg64 register) value = state.write register value := by
  simp [writeOperand]
@[simp, rivet] theorem MachineState.writeOperand_memory (state : MachineState) (width : Width) (address : Address)
    (value : BitVec 64) :
    state.writeOperand (.memory width address) value =
      state.writeMemory (address.evaluate state.registers) width value := by
  simp [writeOperand]
@[simp, rivet] theorem MachineState.writeOperand_immediate (state : MachineState) (operand : Int) (value : BitVec 64) :
    state.writeOperand (.immediate operand) value = state := by
  simp [writeOperand]

-- Register aliases name their parent: `Reg32.edx.parent` is `.rdx`. Syntax only, so
-- these stay open; they are in the `rivet` set but not the default simp set.
attribute [rivet] Reg8.parent Reg16.parent Reg32.parent

/-! ## Effective addresses

One equation per address shape, as word arithmetic over the registers it names.
Only in the `rivet` set. With the word lemmas below, a literal displacement ends as
`r .rbx + 8#64` or `r .rbx - 8#64`, and a zero displacement disappears. -/

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

-- Literal displacements and access sizes as words: `BitVec.ofInt 64 (-8)` becomes a
-- subtraction of `8#64`, and a zero displacement is dropped.
attribute [rivet] Width.bytes BitVec.ofInt_ofNat BitVec.ofInt_neg BitVec.ofInt_natCast
  BitVec.add_neg_eq_sub BitVec.add_zero

end Rivet
