# Rivet

A Lean library for reasoning about restricted Intel-syntax x86-64 assembly. Programs retain instruction operands, widths, source lines, and resolved branch targets. Lean is the only required toolchain; its version is pinned in `lean-toolchain`.

```sh
lake build
```

`import Rivet` provides the whole library. `Rivet.Model` defines the public `MachineState` and execution functions; `Rivet.Contracts` defines composable `Ensures` contracts and instruction rules proved against that interpreter. The API also exposes fault absorption, monotone read histories, and preservation of registers untouched by a program. `Rivet.Parser` defines the accepted source grammar. `Rivet.Safety` and `Rivet.Word` provide generic register-preservation, read-history, and machine-word invariants.

The interpreter and contracts use the same state record. Access registers with `state.registers .rax`, memory with `state.memory address`, and execution status with `state.status`. Status is `.running instructionIndex`, `.returned address`, or `.fault`; there is no observation wrapper or separate proof-state representation.

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
