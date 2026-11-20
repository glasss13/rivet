module
public import Lz4RoundTripImage
@[expose] public section
namespace Rivet.Lz4RoundTripProof

-- The caller's choices for `roundtrip(input, compressed, output, size, capacity)`, which compresses
-- `size` bytes of `input` into `compressed` with LZ4_compress_default and decompresses them into
-- `output` with LZ4_decompress_safe, returning what LZ4_decompress_safe returns. The two sizes are
-- the low 32 bits of C `int` arguments. The bounds are deployment assumptions of this benchmark, not
-- x86 restrictions: every byte the caller supplies lies at or above 65536 and below 2^47. The stack's
-- bound covers the 16656 bytes of workspace below the entry RSP and the eight-byte return slot at it.
structure Arguments where
  inputAddress : BitVec 64
  inputSize : BitVec 32
  compressedAddress : BitVec 64
  compressedCapacity : BitVec 32
  outputAddress : BitVec 64
  stackPointer : BitVec 64
  returnAddress : BitVec 64
  inputBounds : 65536 ≤ inputAddress.toNat ∧ inputAddress.toNat + inputSize.toNat ≤ 2^47
  compressedBounds : 65536 ≤ compressedAddress.toNat ∧ compressedAddress.toNat + compressedCapacity.toNat ≤ 2^47
  outputBounds : 65536 ≤ outputAddress.toNat ∧ outputAddress.toNat + inputSize.toNat ≤ 2^47
  stackBounds : 65536 + 16656 ≤ stackPointer.toNat ∧ stackPointer.toNat + 8 ≤ 2^47

-- The input, the compressed buffer, the output (as long as the input), and the stack from the bottom
-- of the workspace below the entry RSP to the end of the caller's eight-byte return slot. The
-- workspace holds `roundtrip`'s three pushes (24) and its CALL (8), then LZ4_compress_default's
-- state (16424) and its CALL (8), LZ4_compress_fast_extState's six pushes (48) and locals (136), and
-- the CALL of memset or memcpy (8); LZ4_decompress_safe, reached by a tail jump, uses less. That
-- this is enough is part of the proof, not an assumption about execution.
abbrev input (arguments : Arguments) : Region :=
  Region.root arguments.inputAddress arguments.inputSize.toNat true false (by have := arguments.inputBounds; omega)
abbrev compressed (arguments : Arguments) : Region :=
  Region.root arguments.compressedAddress arguments.compressedCapacity.toNat true true
    (by have := arguments.compressedBounds; omega)
abbrev output (arguments : Arguments) : Region :=
  Region.root arguments.outputAddress arguments.inputSize.toNat true true (by have := arguments.outputBounds; omega)
abbrev stack (arguments : Arguments) : Region :=
  Region.root (arguments.stackPointer - 16656#64) 16664 true true (by have := arguments.stackBounds; bv_omega)
abbrev workspace (arguments : Arguments) : Region := (stack arguments).part 0 16656

-- Everything the machine may touch: the ELF's segments, then the buffers and the stack.
def regions (arguments : Arguments) : List Region :=
  Lz4RoundTripImage.regions ++ [input arguments, compressed arguments, output arguments, stack arguments]

def image (arguments : Arguments) : Image := ⟨Lz4RoundTripImage.program, regions arguments⟩

-- Two regions share no byte.
def Apart (first second : Region) : Prop :=
  first.base + first.length ≤ second.base ∨ second.base + second.length ≤ first.base

-- Caller obligations only. The sizes are nonnegative signed 32-bit C ints. The input is at most
-- LZ4_MAX_INPUT_SIZE and the compressed buffer holds at least LZ4_compressBound(size) bytes, as
-- lz4.h documents for a compression that cannot fail. Other registers, the flags, and the bytes of
-- the compressed buffer, the output and the stack are unrestricted, except that the return slot
-- holds the continuation.
structure Preconditions (arguments : Arguments) (initial : MachineState) : Prop where
  entry : initial.status = .running Lz4RoundTripImage.entry
  inputRegister : initial.registers .rdi = arguments.inputAddress
  compressedRegister : initial.registers .rsi = arguments.compressedAddress
  outputRegister : initial.registers .rdx = arguments.outputAddress
  inputSizeRegister : (initial.registers .rcx).setWidth 32 = arguments.inputSize
  compressedCapacityRegister : (initial.registers .r8).setWidth 32 = arguments.compressedCapacity
  stackRegister : initial.registers .rsp = arguments.stackPointer
  -- The System V ABI's alignment at a function's entry: the stack pointer plus 8 is a multiple of 16.
  stackAligned : (arguments.stackPointer.toNat + 8) % 16 = 0
  -- LZ4_MAX_INPUT_SIZE.
  inputSizeFits : arguments.inputSize.toNat ≤ 0x7E000000
  -- LZ4_compressBound(size), and a capacity that is a nonnegative int.
  compressedCapacityFits : arguments.inputSize.toNat + arguments.inputSize.toNat / 255 + 16 ≤
    arguments.compressedCapacity.toNat ∧ arguments.compressedCapacity.toNat < 2^31
  -- The ELF's segments, the buffers and the stack do not overlap.
  disjoint : (regions arguments).Pairwise Apart
  -- Memory holds the ELF's segments, as the loader leaves them.
  loaded : Lz4RoundTripImage.Loaded initial.memory
  returnSlot : initial.returnAddress = arguments.returnAddress

-- Control has returned to the supplied continuation, with RET's stack effect; the result is the
-- input's size, and the output holds the input's bytes as they were at the call.
def Restored (arguments : Arguments) (initial final : MachineState) : Prop :=
  final.status = .running arguments.returnAddress ∧
  final.registers .rsp = arguments.stackPointer + 8#64 ∧
  (final.registers .rax).setWidth 32 = arguments.inputSize ∧
  ∀ offset, offset < arguments.inputSize.toNat →
    readBytes final.memory (arguments.outputAddress + BitVec.ofNat 64 offset) 1 =
      readBytes initial.memory (arguments.inputAddress + BitVec.ofNat 64 offset) 1

-- What a call may change: the caller-saved registers and the stack pointer, the compressed buffer,
-- the output, and the workspace below the entry stack pointer. The return slot is not in it.
def callChanges (arguments : Arguments) : Changes :=
  { registers := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp],
    memory := [compressed arguments, output arguments, workspace arguments] }

-- Every admissible call returns in finitely many instructions, for every undefined-flag choice,
-- with the input's bytes in the output, having changed nothing outside `callChanges`.
def RoundTrip : Prop :=
  ∀ arguments initial, Preconditions arguments initial →
    Block (image arguments) initial (callChanges arguments) (Restored arguments initial)

end Rivet.Lz4RoundTripProof
