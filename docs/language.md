# Restricted language, version 1

Input is UTF-8. Keywords and registers are case-sensitive. Space, tab, CRLF/LF line endings, blank lines, and `#` comments are supported. Commas may have surrounding whitespace. A label occupies its own line. Each instruction occupies one line. Semicolons are rejected outside comments.

Exactly one `.globl NAME` declaration must precede the function label `NAME:`. This is the entire directive whitelist. Identifiers use ASCII letters, digits, and underscore, and cannot start with a digit. Other labels are local to this one function's parsed instruction sequence. Duplicate labels and unresolved or one-past-end branch targets are rejected. A second global declaration is rejected. Local labels do not declare additional functions.

The frozen instruction forms are:

| Source | Parsed operation | Width/effect |
|---|---|---|
| `xor eax, eax` | `xor .eax .eax` | 32-bit zeroing, zero-extended to 64 bits; ZF=1 |
| `test rsi, rsi` | `test .rsi .rsi` | 64-bit zero test; register unchanged |
| `movzx edx, BYTE PTR [rdi]` | `movzx .edx (.bytePtr .rdi)` | Read 8 bits, extend to 32 bits, zero high 32 bits |
| `add rax, rdx` | `add .rax .rdx` | 64-bit modular addition; update ZF |
| `inc rdi` | `inc .rdi` | 64-bit modular increment; update ZF |
| `dec rsi` | `dec .rsi` | 64-bit modular decrement; update ZF |
| `jz LABEL` | `jz index` | Branch if ZF is set |
| `jnz LABEL` | `jnz index` | Branch if ZF is clear |
| `ret` | `ret` | Read 8-byte little-endian return address; RSP += 8 modulo 2^64 |

The opcode names are x86 mnemonics. Width is expressed in the operand types: `Reg32` names the supported 32-bit aliases (`eax`, `edx`), `Reg` names 64-bit registers, and `Mem8.bytePtr` denotes a byte memory operand. Both source operands are retained for `xor` and `test`; their bitwise semantics are defined directly in the shared execution model. Register operands and resolved targets are explicit fields. Instructions also carry their original one-based line number. Diagnostics identify the line where possible; whole-program errors identify the failed condition. No opcode is inferred from intent, and loops are neither summarized nor optimized by the importer.

Even alternate spellings such as `je`, `BYTE ptr`, `ret 8`, `[rdi + 0]`, or `xor rax, rax` are rejected. The shared model has register-parameterized operations for reuse; the source grammar currently admits only the exact operand combinations above. Extend the grammar deliberately, with new differential tests, when widening the supported subset.

There are no macros, includes, conditional assembly, arbitrary directives, indirect branches, external calls, data declarations, code-address instructions, code writes, or instruction separators. The assembler wrapper supplies `.intel_syntax noprefix`, `.text`, and a non-executable-stack note. Nothing else is prepended or substituted.

Importer invocation:

```sh
cargo build --manifest-path importer/Cargo.toml --locked --offline
importer/target/debug/asm-to-lean fixtures/sum_bytes.s Verification/Imported.lean
```

A third positional argument (an ASCII identifier) selects the generated Lean namespace for test fixtures. The generated certificate is `parse source = Except.ok program`, checked with `decide +kernel`. The Rust parser is untrusted: disagreement with the reference parser makes the certificate fail. SHA-256 is provenance metadata checked by the build script, not a cryptographic theorem inside Lean.
