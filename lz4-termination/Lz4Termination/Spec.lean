module
public import Lz4Image
@[expose] public section
namespace Rivet.Lz4Proof

-- The caller's choices. The two sizes are the low 32 bits of C `int` arguments.
structure Arguments where
  inputAddress : BitVec 64
  compressedSize : BitVec 32
  outputAddress : BitVec 64
  outputCapacity : BitVec 32
  stackPointer : BitVec 64
  returnAddress : BitVec 64

-- Deployment assumptions of this benchmark, not x86 restrictions: every byte the
-- caller supplies lies at or above 65536 and below 2^47.
def minimumAddress : BitVec 64 := 0x10000#64
def addressLimit : BitVec 64 := 0x800000000000#64

-- Space below the entry RSP: six pushes (48), locals (56), and CALL (8).
-- That this is enough is part of the proof, not an assumption about execution.
def stackWorkspaceBytes : BitVec 64 := 112#64

-- Everything the machine may touch: the ELF's segments, then the input, the
-- output, and the stack from the bottom of the workspace to the end of the
-- caller's eight-byte return slot. Output is readable because LZ4 copies
-- matches from output it has already produced.
def regions (arguments : Arguments) : List Region :=
  Lz4Image.regions ++ [
    { base := arguments.inputAddress, length := arguments.compressedSize.setWidth 64,
      readable := true, writable := false },
    { base := arguments.outputAddress, length := arguments.outputCapacity.setWidth 64,
      readable := true, writable := true },
    { base := arguments.stackPointer - stackWorkspaceBytes, length := stackWorkspaceBytes + 8#64,
      readable := true, writable := true }]

def image (arguments : Arguments) : Image := ⟨Lz4Image.program, regions arguments⟩

-- Two regions share no byte. Every region below ends at or under `addressLimit`,
-- so neither range wraps.
def Apart (first second : Region) : Prop :=
  first.length ≤ second.base - first.base ∧ second.length ≤ first.base - second.base

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
  compressedSizeFits : arguments.compressedSize < 0x80000000#32
  outputCapacityFits : arguments.outputCapacity < 0x80000000#32
  inputAddressMinimum : minimumAddress ≤ arguments.inputAddress
  inputNoWrap : arguments.inputAddress ≤ arguments.inputAddress + arguments.compressedSize.setWidth 64
  inputEndMaximum : arguments.inputAddress + arguments.compressedSize.setWidth 64 ≤ addressLimit
  outputAddressMinimum : minimumAddress ≤ arguments.outputAddress
  outputNoWrap : arguments.outputAddress ≤ arguments.outputAddress + arguments.outputCapacity.setWidth 64
  outputEndMaximum : arguments.outputAddress + arguments.outputCapacity.setWidth 64 ≤ addressLimit
  stackRoom : stackWorkspaceBytes ≤ arguments.stackPointer
  stackAddressMinimum : minimumAddress ≤ arguments.stackPointer - stackWorkspaceBytes
  stackNoWrap : arguments.stackPointer ≤ arguments.stackPointer + 8#64
  stackEndMaximum : arguments.stackPointer + 8#64 ≤ addressLimit
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
