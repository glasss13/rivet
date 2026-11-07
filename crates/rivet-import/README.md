# Binary importer

`rivet-import` reads all defined function symbols from a linked x86-64 ELF executable,
decodes their code with iced-x86, and writes a Lean module containing `entry : Nat` and
`program : Rivet.Program`. Addresses, encoding lengths, and branch targets come
from the binary. No assembly text is parsed along the way.

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

This imports **function code only**. It does not map ELF segments, initialize
memory, or construct a machine state. Proofs still supply the function's input
memory, stack, registers, and permissions. That is enough for functions such as
ByteSum. RIP-relative references use the binary's addresses; proofs must supply
any referenced data and its permissions in the initial memory. Table contents
are not imported automatically. Loading globals and modeling process startup
can come later. CALL/RET use ordinary stack memory and transfer control; RET does
not stop the interpreter. Proofs specify completion through their postcondition.

The importer and iced-x86 are trusted to translate the bytes correctly. Lean
checks proofs about the generated program; it does not certify that translation
or model instruction fetch from mutable executable memory. Regenerate the module
when the binary changes.
