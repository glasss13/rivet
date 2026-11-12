# Rivet

A Lean 4 library for proving things about x86-64 machine code. You import a compiled
function, state what it should do, and step through its instructions until Lean accepts
the proof.

```sh
lake build
```

## What a theorem says

`Ensures image s Q` means: from the machine state `s`, and for every value the CPU might
leave in its undefined flags, execution reaches a state satisfying `Q` in finitely many
steps. What the start state must satisfy is stated as ordinary hypotheses about `s`. A
fault is permanent, so a `Q` that requires `status = .running …` also proves that nothing
faulted on the way.

What a proof does not cover:

- The decoder. Instructions come from the importer and iced-x86, not from Lean.
- The CPU. The model is tested against real hardware (`cargo run -p rivet-check -- --cases 1000`),
  not proved equal to it.
- Flags other than ZF, CF and SF, instructions outside the supported subset, and concurrency.

## An example

A function that adds its two arguments, using `rbx` as scratch and restoring it.

```lean
module
import Rivet
open Rivet

-- push rbx · mov rbx, rdi · add rbx, rsi · mov rax, rbx · pop rbx · ret
def sum : Program :=
  [⟨0x1000, 1, .push .rbx⟩,
   ⟨0x1001, 3, .mov (.reg64 .rbx) (.reg64 .rdi)⟩,
   ⟨0x1004, 3, .binary .add (.reg64 .rbx) (.reg64 .rsi)⟩,
   ⟨0x1007, 3, .mov (.reg64 .rax) (.reg64 .rbx)⟩,
   ⟨0x100a, 1, .pop .rbx⟩,
   ⟨0x100b, 1, .ret⟩]

theorem sum_correct (regions : List Region) (s : MachineState)
    (entry : s.status = .running 0x1000)
    -- the caller's promise: 16 bytes of stack, the slot `push` uses and the return address
    (write : permits (Image.writable ⟨sum, regions⟩) (s.registers .rsp - 8#64) 16#64 = true)
    (read : permits (Image.readable ⟨sum, regions⟩) (s.registers .rsp - 8#64) 16#64 = true) :
    Ensures ⟨sum, regions⟩ s (fun f =>
      f.status = .running s.returnAddress ∧
      f.registers .rax = s.registers .rdi + s.registers .rsi ∧
      f.registers .rbx = s.registers .rbx ∧
      f.registers .rsp = s.registers .rsp + 8#64) := by
  rivet_step (disch := (apply permits_inside write <;> grind))   -- push rbx
  rivet_step                                                      -- mov rbx, rdi
  rivet_step                                                      -- add rbx, rsi
  rivet_step                                                      -- mov rax, rbx
  rivet_step (disch := (apply permits_inside read <;> grind))    -- pop rbx
  rivet_step (disch := (apply permits_inside read <;> grind))    -- ret
  exact Ensures.done (by
    simp [*, MachineState.returnAddress, BitVec.sub_add_cancel]
    constructor
    · rw [Memory.readBytes_storeBytes_disjoint] <;> grind   -- the return address sits above the saved rbx
    · rw [Memory.readBytes_storeBytes_within] <;> simp)      -- pop reads back what push stored
```

Each `rivet_step` executes one instruction and records what it changed. An instruction
that touches memory asks for a permission; `disch` proves it by naming the region the
access falls in. `Ensures.done` ends the block once the goal holds of the current state.

To work on a real binary, generate the program instead of writing it by hand:

```sh
cargo run -p rivet-import -- ./prog --function sum --namespace Sum --output Sum.lean
```

That gives `Sum.entry`, `Sum.program`, `Sum.regions` for the binary's segments, and
`Sum.Loaded memory`, which says memory holds each segment's bytes.

## API

[API.md](API.md) lists everything a proof can use, by concept.
