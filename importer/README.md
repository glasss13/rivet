# Binary importer

`rivet-import` reads a named function from a linked x86-64 ELF executable, decodes
it with iced-x86, and writes a Lean module containing `entry : Nat` and
`program : Rivet.Program`. Addresses, encoding lengths, and branch targets come
from the binary. No assembly text is parsed along the way.

```sh
cargo run --release --manifest-path importer/Cargo.toml -- ./example \
  --function sum_bytes --namespace Example --output Example.lean
```

The namespace defaults to the function name. Import the generated module into a
proof and use `Example.program` and `Example.entry`. Rust is only needed to run
the importer; checking the generated module and its proofs requires only Lean.

The initial scope is deliberately small:

- Fixed-address, little-endian ELF64 executables, without dynamic loading or
  relocation records. Object files and PIE executables must be linked first.
- A defined function symbol with a nonzero size. Compiler-generated symbol
  tables suffice; debug information is unnecessary. Stripped files are not
  supported. Handwritten assembly needs `.type name,@function` and
  `.size name,.-name` directives.
- Scalar MOV, ADD/SUB/SBB/CMP/TEST/AND/OR/XOR; 64-bit LEA, INC/DEC and register
  PUSH/POP; MOVZX into 32-bit registers; MOVSXD into 64-bit registers; plain RET;
  and direct JMP/JE/JNE/JB/JAE/JBE/JA/JS within the selected function.
- Register aliases and 64-bit base/index/displacement addressing supported by
  Rivet. High-byte registers, RIP-relative addressing, address-size overrides,
  segment overrides, LOCK/REP prefixes, SIMD, and calls are rejected.

Every byte in the symbol's range must decode into a supported instruction;
embedded data and unsupported padding instructions are rejected. Direct branches
must land at instruction boundaries within that range. Errors report the
instruction address, and translation errors leave the output file untouched.

This imports **function code only**. It does not map ELF segments, initialize
memory, or construct a machine state. Proofs still supply the function's input
memory, stack, registers, and permissions. That is enough for functions such as
ByteSum; loading globals and modeling process startup can come later. RET retains
Rivet's function-level successful-return semantics.

The importer and iced-x86 are trusted to translate the bytes correctly. Lean
checks proofs about the generated program; it does not certify that translation
or model instruction fetch from mutable executable memory. Regenerate the module
when the binary changes.
