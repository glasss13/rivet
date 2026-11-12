module
public import Lz4Image
@[expose] public section
namespace Rivet.Lz4Proof

-- The caller's choices. The two sizes are the low 32 bits of C `int` arguments.
-- The three bounds are deployment assumptions of this benchmark, not x86
-- restrictions: every byte the caller supplies lies at or above 65536 and below
-- 2^47. The stack's bound covers the 112 bytes of workspace below the entry RSP
-- and the eight-byte return slot at it.
structure Arguments where
  inputAddress : BitVec 64
  compressedSize : BitVec 32
  outputAddress : BitVec 64
  outputCapacity : BitVec 32
  stackPointer : BitVec 64
  returnAddress : BitVec 64
  inputBounds : 65536 ≤ inputAddress.toNat ∧ inputAddress.toNat + compressedSize.toNat ≤ 2^47
  outputBounds : 65536 ≤ outputAddress.toNat ∧ outputAddress.toNat + outputCapacity.toNat ≤ 2^47
  stackBounds : 65536 + 112 ≤ stackPointer.toNat ∧ stackPointer.toNat + 8 ≤ 2^47

-- Space below the entry RSP: six pushes (48), locals (56), and CALL (8).
-- That this is enough is part of the proof, not an assumption about execution.
def stackWorkspaceBytes : Nat := 112

-- Everything the machine may touch: the ELF's segments, then the input, the
-- output, and the stack from the bottom of the workspace to the end of the
-- caller's eight-byte return slot. Output is readable because LZ4 copies
-- matches from output it has already produced.
def regions (arguments : Arguments) : List Region :=
  Lz4Image.regions ++ [
    { base := arguments.inputAddress.toNat, length := arguments.compressedSize.toNat,
      readable := true, writable := false, fits := by have := arguments.inputBounds; omega },
    { base := arguments.outputAddress.toNat, length := arguments.outputCapacity.toNat,
      readable := true, writable := true, fits := by have := arguments.outputBounds; omega },
    { base := arguments.stackPointer.toNat - stackWorkspaceBytes, length := stackWorkspaceBytes + 8,
      readable := true, writable := true,
      fits := by have := arguments.stackBounds; simp only [stackWorkspaceBytes]; omega }]

def image (arguments : Arguments) : Image := ⟨Lz4Image.program, regions arguments⟩

-- Two regions share no byte.
def Apart (first second : Region) : Prop :=
  first.base + first.length ≤ second.base ∨ second.base + second.length ≤ first.base

-- Caller obligations only. The sizes are nonnegative signed 32-bit C ints. Other
-- registers, the flags, and the bytes of the input, output and stack are
-- unrestricted, except that the return slot holds the continuation.
structure Preconditions (arguments : Arguments) (initial : MachineState) : Prop where
  entry : initial.status = .running Lz4Image.entry
  inputRegister : initial.registers .rdi = arguments.inputAddress
  outputRegister : initial.registers .rsi = arguments.outputAddress
  compressedSizeRegister : (initial.registers .rdx).setWidth 32 = arguments.compressedSize
  outputCapacityRegister : (initial.registers .rcx).setWidth 32 = arguments.outputCapacity
  stackRegister : initial.registers .rsp = arguments.stackPointer
  compressedSizeFits : arguments.compressedSize.toNat < 2^31
  outputCapacityFits : arguments.outputCapacity.toNat < 2^31
  -- The ELF's segments, the buffers and the stack do not overlap.
  disjoint : (regions arguments).Pairwise Apart
  -- Memory holds the ELF's segments, as the loader leaves them.
  loaded : Lz4Image.Loaded initial.memory
  returnSlot : initial.returnAddress = arguments.returnAddress

-- Control has returned to the supplied continuation, with RET's stack effect.
-- There is deliberately no constraint on the return value or output bytes.
def Returned (arguments : Arguments) (state : MachineState) : Prop :=
  state.status = .running arguments.returnAddress ∧
  state.registers .rsp = arguments.stackPointer + 8#64

-- Every admissible call returns in finitely many instructions, for every
-- undefined-flag choice supply. No instruction budget is supplied by callers.
def Termination : Prop :=
  ∀ arguments initial, Preconditions arguments initial →
    Ensures (image arguments) initial (Returned arguments)

end Rivet.Lz4Proof
