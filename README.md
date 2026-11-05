# Assembly verification MVP

This project imports a restricted Intel-syntax x86-64 function and proves its behavior in Lean. The proof target is the generated instruction list, certified equal to parsing the embedded source with the shared Lean parser.

Run the complete acceptance workflow on x86-64 Linux:

```sh
python3 scripts/verify.py
```

Install the versions in `tools.lock.json` and the Lean toolchain in `lean-toolchain` first (`elan toolchain install leanprover/lean4:v4.30.0`). The Rust compiler and Cargo versions are pinned in `tools.lock.json`; the importer has no external crates. There are no third-party Lean or Python packages. The workflow checks the native and Rust tool versions, tests/builds the Rust importer offline with its lockfile, regenerates all imports, builds Lean and the test executables, audits theorem dependencies, and runs native and parser validation. `lake build` alone checks the existing artifacts; it does **not** regenerate them. Always use the workflow after changing assembly.

The fixture is `fixtures/sum_bytes.s`. Native assembly uses exactly those bytes between fixed syntax/section wrappers. No preprocessing or C compilation produces the verified function. The Rust importer (`importer/src/main.rs`) records the UTF-8 source and SHA-256 and emits a kernel-checked parsing certificate. Identical bytes produce identical generated Lean text; generated files contain no timestamps or absolute paths.

The checked results are:

- `sum_bytes_correct`: return after `5 * length + 4` steps, exact mathematical sum, supplied return address, stack adjustment, and exact read trace.
- `all_accesses_safe`: every execution prefix reads only the buffer and return slot (apart from any history already present at entry).
- `empty_reads_only_stack`: zero-length input performs no buffer reads.
- `callee_saved`: RBX, RBP, R12–R15 remain unchanged at every step count.
- `run_memory`: memory is unchanged for every program in the model. There are no memory-writing instructions.
- `never_faults`, `stays_returned`: no modeled fault at any step count, and execution remains returned after completion.
- `run_registers64`: the 64-bit register representation invariant is preserved.

`loop_correct` is an induction over the decreasing remaining count. Its invariant connects the accumulator to the sum still to be consumed, the current address, and the remaining length. `sum_bound` proves the mathematical byte sum is at most `255 * length`; with length at most 4096 the maximum is 1,044,480. The proof explicitly discharges arithmetic wraparound obligations.

Validation covers four buffer patterns at every length 0–4096, null and inaccessible pointers at length zero, 320 instruction-level model/native comparisons including word boundaries and both ZF states, and a native return/stack probe. Two faulty fixtures have concrete Lean and native counterexamples. Parser tests reject unsupported directives, preprocessing, instructions, operand forms, duplicate labels, missing/out-of-range targets, and instruction separators. A tampered generated representation fails Lean checking.

The generated instructions use x86 mnemonics and operand names: `xor eax, eax` becomes `.xor .eax .eax`, and `movzx edx, BYTE PTR [rdi]` becomes `.movzx .edx (.bytePtr .rdi)`. This is a typed syntax tree of the restricted x86 program. It retains both operands, the operand widths, and the instruction order. Branch labels become instruction indices, with the original source retained alongside the tree. The Rust importer performs no instruction lowering or semantic optimization.

To run just the importer:

```sh
cargo build --manifest-path importer/Cargo.toml --locked --offline
importer/target/debug/asm-to-lean fixtures/sum_bytes.s Verification/Imported.lean
```

Python remains only for build/test orchestration; assembly parsing and Lean artifact generation are Rust. The reference parser remains in Lean so the generated representation can be checked by the kernel.

See [the language definition](docs/language.md) and [the assumptions and trust boundary](docs/assumptions.md). The shared foundation is `Verification/Parser.lean` and `Verification/Model.lean`; the specification and proofs are in `Verification/Proof.lean`, `Safety.lean`, and `Word.lean`. `Counterexamples.lean` checks the faulty programs, each with its own parsing certificate.
