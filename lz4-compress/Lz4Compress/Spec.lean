module
public import Lz4CompressImage
@[expose] public section
namespace Rivet.Lz4CompressProof

-- The caller's choices. The two sizes are the low 32 bits of C `int` arguments.
-- The three bounds are deployment assumptions of this benchmark, not x86
-- restrictions: every byte the caller supplies lies at or above 65536 and below
-- 2^47. The stack's bound covers the 16624 bytes of workspace below the entry RSP
-- and the eight-byte return slot at it.
structure Arguments where
  inputAddress : BitVec 64
  inputSize : BitVec 32
  outputAddress : BitVec 64
  outputCapacity : BitVec 32
  stackPointer : BitVec 64
  returnAddress : BitVec 64
  inputBounds : 65536 ≤ inputAddress.toNat ∧ inputAddress.toNat + inputSize.toNat ≤ 2^47
  outputBounds : 65536 ≤ outputAddress.toNat ∧ outputAddress.toNat + outputCapacity.toNat ≤ 2^47
  stackBounds : 65536 + 16624 ≤ stackPointer.toNat ∧ stackPointer.toNat + 8 ≤ 2^47

-- The input, the output, and the stack from the bottom of the workspace below the entry RSP to the
-- end of the caller's eight-byte return slot. The workspace holds LZ4_compress_default's state (16424)
-- and its CALL (8), LZ4_compress_fast_extState's six pushes (48) and locals (136), and the CALL of
-- memset or memcpy (8); that this is enough is part of the proof, not an assumption about execution.
abbrev input (arguments : Arguments) : Region :=
  Region.root arguments.inputAddress arguments.inputSize.toNat true false (by have := arguments.inputBounds; omega)
abbrev output (arguments : Arguments) : Region :=
  Region.root arguments.outputAddress arguments.outputCapacity.toNat true true (by have := arguments.outputBounds; omega)
abbrev stack (arguments : Arguments) : Region :=
  Region.root (arguments.stackPointer - 16624#64) 16632 true true (by have := arguments.stackBounds; bv_omega)
abbrev workspace (arguments : Arguments) : Region := (stack arguments).part 0 16624

-- Everything the machine may touch: the ELF's segments, then the input, the output and the stack.
def regions (arguments : Arguments) : List Region :=
  Lz4CompressImage.regions ++ [input arguments, output arguments, stack arguments]

def image (arguments : Arguments) : Image := ⟨Lz4CompressImage.program, regions arguments⟩

-- Two regions share no byte.
def Apart (first second : Region) : Prop :=
  first.base + first.length ≤ second.base ∨ second.base + second.length ≤ first.base

-- Caller obligations only. The sizes are nonnegative signed 32-bit C ints. Other
-- registers, the flags, and the bytes of the input, output and stack are
-- unrestricted, except that the return slot holds the continuation.
structure Preconditions (arguments : Arguments) (initial : MachineState) : Prop where
  entry : initial.status = .running Lz4CompressImage.entry
  inputRegister : initial.registers .rdi = arguments.inputAddress
  outputRegister : initial.registers .rsi = arguments.outputAddress
  inputSizeRegister : (initial.registers .rdx).setWidth 32 = arguments.inputSize
  outputCapacityRegister : (initial.registers .rcx).setWidth 32 = arguments.outputCapacity
  stackRegister : initial.registers .rsp = arguments.stackPointer
  -- The System V ABI's alignment at a function's entry: the stack pointer plus 8 is a multiple of 16.
  stackAligned : (arguments.stackPointer.toNat + 8) % 16 = 0
  inputSizeFits : arguments.inputSize.toNat < 2^31
  outputCapacityFits : arguments.outputCapacity.toNat < 2^31
  -- The ELF's segments, the buffers and the stack do not overlap.
  disjoint : (regions arguments).Pairwise Apart
  -- Memory holds the ELF's segments, as the loader leaves them.
  loaded : Lz4CompressImage.Loaded initial.memory
  returnSlot : initial.returnAddress = arguments.returnAddress

-- Control has returned to the supplied continuation, with RET's stack effect.
-- There is deliberately no constraint on the return value or output bytes.
def Returned (arguments : Arguments) (state : MachineState) : Prop :=
  state.status = .running arguments.returnAddress ∧
  state.registers .rsp = arguments.stackPointer + 8#64

-- What a call may change: the caller-saved registers and the stack pointer, the output buffer,
-- and the workspace below the entry stack pointer. The return slot is not in it.
def callChanges (arguments : Arguments) : Changes :=
  { registers := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp],
    memory := [output arguments, workspace arguments] }

-- Every admissible call returns in finitely many instructions, for every undefined-flag choice,
-- having changed nothing outside `callChanges`. No instruction budget is supplied by callers.
def Termination : Prop :=
  ∀ arguments initial, Preconditions arguments initial →
    Block (image arguments) initial (callChanges arguments) (Returned arguments)

end Rivet.Lz4CompressProof
