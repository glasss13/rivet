# Rivet

A Lean library for reasoning about restricted Intel-syntax x86-64 assembly. Programs retain instruction operands, widths, source lines, and resolved branch targets. Lean is the only required toolchain; its version is pinned in `lean-toolchain`.

```sh
lake build
```

`import Rivet` provides the whole library. `Rivet.Model` defines the public `MachineState` and execution functions; `Rivet.Contracts` defines uncounted block contracts (`Ensures`), successful function contracts (`Returns`), and instruction rules proved against that interpreter. The API also exposes fault absorption, monotone read histories, and preservation of registers untouched by a program. `Rivet.Parser` defines the accepted source grammar. `Rivet.Safety` provides generic register-preservation and read-history properties. Registers have type `BitVec 64`, so register width is guaranteed by construction.

The interpreter and contracts use the same state record. Access registers with `state.registers .rax`, natural-number values with `(state.registers .rax).toNat`, memory with `state.memory address`, and execution status with `state.status`. Status is `.running instructionIndex`, `.returned address`, or `.fault`; there is no observation wrapper or separate proof-state representation.

Proof contracts separate reachability, successful return, and ongoing safety:

- `Reaches program initial final` means some finite number of interpreter steps reaches `final`. It includes zero steps and is equivalent by definition to `∃ steps, execute program steps initial = final`.
- `Ensures program precondition postcondition` means every state satisfying the precondition eventually reaches a state satisfying the postcondition. This is a block contract: its postcondition can describe an intermediate instruction. `Ensures.refl` permits zero steps; it establishes no successful return by itself.
- `Returns program precondition postcondition` additionally requires the final status to be `.returned address` for some address. Use `contract.returns` with a proof that the block's postcondition implies return. A postcondition already true initially cannot establish `Returns` from a running or faulted state without reaching a successful return.
- `Always program initial property` states that the property holds at every finitely reachable state, including the initial state. `Always.induction` proves this from an initial fact and preservation by `step`.
- `Diverges program initial` means every finite prefix remains running. `Diverges.of_progress` accepts an invariant whose states are running and, after taking one instruction, can reach another invariant state. This guarantees positive progress without a step-count witness. Zero-step reachability and stopped-state stuttering cannot establish divergence.

Instruction rules such as `clear`, `read_byte`, and `return_` produce `Ensures` contracts describing the resulting state. Compose them with `first.seq second` and adapt predicates with `contract.consequence`; neither operation exposes instruction counts. `contract.run initial assumption` yields `∃ final, Reaches program initial final ∧ postcondition final`. For a `Returns` contract, the postcondition also contains the successful-return fact.

`Ensures.loop invariant finished measure body` iterates blocks until `finished` holds. For each invariant state where it does not hold, `body` must establish another invariant state with a strictly smaller natural-valued measure. Measures can describe algorithmic progress, such as bytes remaining. Ordinary induction over such a measure also composes directly with the instruction rules.

`Reaches.to_return` uses determinism to show that every state reachable from an initial state can still reach its eventual successful return. Together with `Reaches.reads_mono`, `Reaches.not_fault`, and `Reaches.preserves_register`, this supports safety proofs for all execution prefixes without calculating a return budget.

`execute program steps initial` remains available for low-level bounded execution. The native differential validator uses `step` directly to compare intermediate states within its instruction budget. Proof contracts use uncounted execution.

Define a program directly from assembly in your proof module:

```lean
import Rivet
open Rivet

def source : String := include_str "input.s"
def program : Program := (parse source).toOption.get (by decide +kernel)
```

`include_str` embeds the file contents at elaboration time, relative to the Lean source file. The proof argument checks that parsing succeeded; invalid assembly cannot silently become an empty program. There is no generated instruction-list file or separate translation implementation. Recompile the containing Lean module after changing its assembly input.

The source grammar accepts `xor eax, eax`, `test rsi, rsi`, `movzx edx, BYTE PTR [rdi]`, `add rax, rdx`, `inc rdi`, `dec rsi`, `jz LABEL`, `jnz LABEL`, and `ret`, with one initial `.globl NAME` declaration. Other directives and instruction forms are rejected. Intel expression and type keywords are forbidden as label names, regardless of case.

Proofs concern the shared model. Assembler and processor correspondence remain assumptions; machine code is not verified. Only ZF is modeled, memory is read-only, and executions have no concurrency or asynchronous interference.

A developer-only [differential validation harness](validation/README.md) compares the interpreter with native x86-64 execution. Its Rust and Linux tooling requirements are separate from library use.
