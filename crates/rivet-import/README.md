# Binary importer

`rivet-import` reads all defined function symbols from a linked x86-64 ELF executable,
decodes their code with iced-x86, and writes a Lean module containing `entry : Nat`,
`program : Rivet.Program`, and `regions : List Rivet.MemoryRegion`. Addresses,
instruction encodings, and initial segment data come from the binary. No assembly
text is parsed along the way.

`program` is emitted as a chain of suffixes (`program.suffix_<address>`, listed
last to first because each refers to the next) with one Lean-checked step per
instruction (`program.from_<address>`). These let proofs, including `rivet_step`,
fetch any instruction in time independent of the program size. Instructions are
emitted in strictly increasing address order, which the steps rely on.

```sh
cargo run --release -p rivet-import -- ./example \
  --function sum_bytes --namespace Example --output Example.lean
```

`--function` selects the entry point; it does not restrict which functions are
imported. The namespace defaults to that function name. Import the generated
module into a proof and use `Example.program` and `Example.entry`. Rust is only needed to run
the importer; checking the generated module and its proofs requires only Lean.

The crate also exposes `rivet_import::decode(bytes, base_address)`, returning
`Vec<Instruction>` with absolute addresses and structured operations. Shared
instruction, operand, and register types live in `program`, `operand`, and
`register`. They support Serde serialization for the validator's existing Lean
JSON protocol. ELF handling and Lean source emission belong to the CLI; the
library only needs a contiguous code range and its starting address.
Decode at the actual load address: resolved RIP-relative references must be
regenerated if the code moves. `decode` does not require targets to lie inside
its byte range; the CLI validates them against the combined program.

The supported scope is deliberately small:

- Fixed-address, little-endian ELF64 executables, without dynamic loading or
  relocation records. Object files and PIE executables must be linked first.
- Non-overlapping `PT_LOAD` ranges with valid file bounds, file size no greater
  than memory size, and no address overflow. Writable executable segments are
  rejected because instruction fetch uses a fixed decoded program.
- Defined function symbols with nonzero sizes. Exact aliases are deduplicated;
  other overlapping ranges and indirect function resolvers are rejected.
  Compiler-generated symbol tables suffice; debug information is unnecessary. Stripped files are not
  supported. Handwritten assembly needs `.type name,@function` and
  `.size name,.-name` directives.
- Scalar MOV, ADD/SUB/SBB/CMP/TEST/AND/OR/XOR; 64-bit LEA, INC/DEC and register
  PUSH/POP; MOVZX into 32-bit registers; MOVSXD into 64-bit registers; plain RET;
  direct CALL; and direct JMP/JE/JNE/JB/JAE/JBE/JA/JS across imported functions.
- Single-byte and multi-byte NOPs, including segment/address-size prefixes used
  for padding. NOP advances by its encoded length without accessing memory or
  changing registers or flags.
- NOT on scalar registers or memory; two/three-operand IMUL at 16/32/64 bits;
  SHL/SHR on 32/64-bit registers with immediate counts (including the implicit
  count-one encoding). CL counts and memory shifts are rejected.
- SETcc and CMOVcc for E/NE/B/AE/BE/A/S, matching Rivet's modeled flags.
- Legacy MOVUPS/MOVDQU between memory and XMM registers, MOVD from a 32-bit
  general-purpose register into XMM, and PSHUFD between XMM registers with an
  immediate selector. Other SIMD forms, including AVX, are rejected.
- Register aliases, 64-bit base/index/displacement addressing, and RIP-relative
  operands resolved to absolute addresses. High-byte registers, address-size
  overrides and segment overrides (except on NOP), LOCK/REP prefixes, indirect/far
  calls, and RET with a stack-adjustment immediate are rejected. Mandatory SSE
  prefixes are decoded as part of their instruction, not as REP operations.

Every byte in each function's range must decode into a supported instruction;
embedded data and unsupported padding instructions are rejected. Direct calls
and branches must land at instruction boundaries in the combined program. Unrelated functions
with unsupported instructions also cause import to fail; link only the code you
need (for example, using function sections and linker garbage collection).
Errors report the instruction address, and translation errors leave the output file untouched.

Each loadable segment becomes a `MemoryRegion` with `address`, `size`, `contents`,
`readable`, and `writable`. `contents` maps byte offsets to `Fin 256` values.
Imported contents use a `ByteArray` and return zero past its end, so BSS does not
expand the generated source. Handwritten regions can use symbolic byte functions.

Construct the complete memory layout before constructing the machine state:

```lean
def initial (registers : Rivet.Reg → BitVec 64)
    (stack input output : Rivet.MemoryRegion) : Except String Rivet.MachineState := do
  let memory ← Rivet.Memory.ofRegions (Example.regions ++ [stack, input, output])
  return {
    memory
    registers
    zeroFlag := false
    status := .running Example.entry
    readHistory := [] }
```

`Memory.ofRegions` rejects overlap and addresses beyond the 64-bit address space.
A `Memory` also carries its layout validity proof, so direct record construction
must establish the same invariant. For concrete layouts, the `valid` field is
proved automatically; symbolic layouts can supply that proof explicitly.

`MachineState.memory` is a `Memory`, not an unrestricted byte function. It remains
callable as `state.memory address`; `state.readable` and `state.writable` derive
permissions from its regions. Addresses outside every region are inaccessible
and inspect as zero. Buffers that alias should share a region rather than declare
overlapping regions. Stores change contents without changing layout or permissions.
Low-level store helpers rely on instruction semantics to check write permissions.
`initializeMemory` and the separate permission fields are removed.

These are the ELF-declared byte ranges and read/write flags, not an exact Linux
page map. Page rounding, shared boundary pages, dynamic loading, process startup,
and OS permission adjustments are not modeled. Executable flags still determine
which segments can supply decoded instructions; the state has no executable
permission field. CALL/RET transfer control normally; completion is specified
by the proof's postcondition.

The importer and iced-x86 are trusted to translate the bytes correctly. Lean
checks proofs about the generated program; it does not certify that translation
or model instruction fetch from mutable executable memory. Regenerate the module
when the binary changes.
