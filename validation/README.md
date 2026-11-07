# Rivet differential validation

Developer-only harness for **x86-64 Linux**. Rust compares actual CPU execution against Rivet's compiled Lean interpreter; it contains no reference implementation of the instruction semantics.

Requires the repository's Lean toolchain, stable Rust/Cargo, GNU assembler (`as`), and permission to trace a child with `ptrace`. The root `lake build` remains Lean-only.

The bridge uses [lean-json](https://github.com/paulbutcher/lean-json) for JSON and automatic codecs; its deriving support is imported only at compile time.

From the repository root:

```sh
cargo run --locked --manifest-path validation/Cargo.toml -- --cases 1000 --seed 20261105
```

This builds the Lean model and generates cases from a seeded random generator biased toward arithmetic boundaries. The harness checks individual instructions with varied operands, short branching programs, and randomized matched PUSH/POP save/restore sequences ending in RET. Whole programs run for at most 64 instructions; loops may return, fault, or remain running at that limit. RSI, the generated countdown register, is sometimes initialized to a small value to exercise terminating loops. Lean always receives structured instructions; native execution uses assembly generated from those same instructions. Branching programs preserve the return stack and use RDI as their data pointer; stack sequences restore the original return slot.

Each case is prepared once in `setup.rs`, producing two separate values: `ExecutionInput` is plain program and initial-state data; `NativeMemory` owns the executable code and data/stack allocations. Native execution receives both. Lean receives only `ExecutionInput`, so it can run independently of the native resources.

After each instruction it compares all sixteen general-purpose registers, ZF, CF, SF, instruction location, return/fault status, and every byte of the controlled data/stack memory. The parent reads the stopped child’s memory through `/proc/PID/mem`, so copy-on-write pages are observed correctly. Randomly read-only data pages and accesses around an inaccessible guard page exercise store, load, and return faults, including multi-byte accesses whose first byte is accessible. Assembler symbols determine native instruction boundaries independently of Rivet.

Multi-instruction programs start RSP on a controlled stack. Individual PUSH/POP cases place the accessed slot in data or near the guard page to exercise unaligned accesses, read-only memory, and faults. All sixteen registers, including RSP itself, are generated. MOV and scalar arithmetic/logic generation cover register, immediate, load, and store forms at 8/16/32/64 bits, including partial-register writes, scaled indices, signed displacements, and unaligned accesses. MOVZX covers byte/word register and memory sources; MOVSXD covers dword register and memory sources. SETcc covers byte register and memory destinations; CMOVcc covers 16/32/64-bit registers and memory sources. All seven supported conditions are generated for jumps, SETcc, and CMOVcc, with random initial flags. Unconditional jumps also exercise loops. The comparison includes false-condition CMOV loads, access faults, and 32-bit destination zero-extension. LEA uses the same address expressions without memory access, including arbitrary register values that can produce wrapped or noncanonical addresses. Load/store base registers are initialized near controlled data or the guard boundary; index registers receive small offsets (or a mapped address for index-only operands). Replay recreates these bindings so it works across different ASLR addresses.

A mismatch prints the seed, case number, and case JSON. Instructions use the named operands from Rivet’s instruction types: `{"binary": {"operation": "add", "destination": {"reg64": {"register": "rax"}}, "source": {"reg64": {"register": "rdx"}}}}`, `{"inc": {"destination": "rdi"}}`, or `"ret"`. MOV operands and addresses are defined in [operand.rs](src/operand.rs), using the typed registers in [register.rs](src/register.rs); register-value arrays follow the declaration order of `Register64`. Save the case JSON to rerun it:

```sh
cargo run --locked --manifest-path validation/Cargo.toml -- --replay /tmp/case.json
```

Exit codes: **0** = passed; **1** = semantic mismatch; **2** = infrastructure, protocol, or invalid-input error.

The native runner forks a traced child per case and single-steps it with a two-second stop deadline. Each model invocation has a five-second deadline, including pipe I/O. Both processes are cleaned up on errors.

This is bounded observational testing. It checks ZF, CF, and SF rather than all RFLAGS, compares generic fault status, and does not observe memory-read events or memory outside the controlled pages. Reaching the instruction budget compares an execution prefix; it does not prove termination.
