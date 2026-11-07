# Rivet differential validation

Developer-only harness for **x86-64 Linux**. Rust compares actual CPU execution against Rivet's compiled Lean interpreter; it contains no reference implementation of the instruction semantics.

Requires the repository's Lean toolchain, stable Rust/Cargo, GNU assembler (`as`), and permission to trace a child with `ptrace`. The root `lake build` remains Lean-only.

The bridge uses [lean-json](https://github.com/paulbutcher/lean-json) for JSON and automatic codecs; its deriving support is imported only at compile time.

From the repository root:

```sh
cargo run --locked --manifest-path validation/Cargo.toml -- --cases 1000 --seed 20261105
```

This builds the Lean model and generates cases from a seeded random generator biased toward arithmetic boundaries. The harness checks individual instructions with varied operands and short programs with forward, backward, and self branches and a final RET. Whole programs run for at most 64 instructions; loops may return, fault, or remain running at that limit. RSI, the generated countdown register, is sometimes initialized to a small value to exercise terminating loops. Lean always receives structured instructions; native execution uses assembly generated from those same instructions. Program generation preserves the return stack and uses RDI as its data pointer.

Each case is prepared once in `setup.rs`, producing two separate values: `ExecutionInput` is plain program and initial-state data; `NativeMemory` owns the executable code and data/stack allocations. Native execution receives both. Lean receives only `ExecutionInput`, so it can run independently of the native resources.

After each instruction it compares all sixteen general-purpose registers, ZF, CF, instruction location, return/fault status, and every byte of the controlled data/stack memory. The parent reads the stopped child’s memory through `/proc/PID/mem`, so copy-on-write pages are observed correctly. Randomly read-only data pages and accesses around an inaccessible guard page exercise store, load, and return faults, including multi-byte accesses whose first byte is accessible. Assembler symbols determine native instruction boundaries independently of Rivet.

RSP starts on a controlled stack. MOV generation covers register, immediate, load, and store forms at 8/16/32/64 bits, including partial-register writes, scaled indices, signed displacements, and unaligned accesses. Load/store base registers are initialized near controlled data or the guard boundary; index registers receive small offsets (or a mapped address for index-only operands). Replay recreates these bindings so it works across different ASLR addresses.

A mismatch prints the seed, case number, and case JSON. Instructions use the named operands from Rivet’s instruction types: `{"add": {"destination": "rax", "source": "rdx"}}`, `{"inc": {"destination": "rdi"}}`, or `"ret"`. MOV operands and addresses are defined in [operand.rs](src/operand.rs), using the typed registers in [register.rs](src/register.rs); register-value arrays follow the declaration order of `Register64`. Save the case JSON to rerun it:

```sh
cargo run --locked --manifest-path validation/Cargo.toml -- --replay /tmp/case.json
```

Exit codes: **0** = passed; **1** = semantic mismatch; **2** = infrastructure, protocol, or invalid-input error.

The native runner forks a traced child per case and single-steps it with a two-second stop deadline. Each model invocation has a five-second deadline, including pipe I/O. Both processes are cleaned up on errors.

This is bounded observational testing. It checks ZF and CF rather than all RFLAGS, compares generic fault status, and does not observe memory-read events or memory outside the controlled pages. Reaching the instruction budget compares an execution prefix; it does not prove termination.
