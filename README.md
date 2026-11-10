# Rivet

A Lean 4 library for proving things about x86-64 machine code. You import a compiled
function, state what it should do, and step through its instructions until Lean accepts
the proof.

```sh
lake build
```

## What a theorem says

`Ensures image P Q` means: from every machine state satisfying `P`, and for every value
the CPU might leave in its undefined flags, execution reaches a state satisfying `Q` in
finitely many steps. A fault is permanent, so a `Q` that requires `status = .running …`
also proves that nothing faulted on the way.

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
    Ensures ⟨sum, regions⟩ (· = s) (fun f =>
      f.status = .running s.returnAddress ∧
      f.registers .rax = s.registers .rdi + s.registers .rsi ∧
      f.registers .rbx = s.registers .rbx ∧
      f.registers .rsp = s.registers .rsp + 8#64) := by
  rivet_step (disch := (apply permits_inside write <;> bv_omega))   -- push rbx
  rivet_step                                                         -- mov rbx, rdi
  rivet_step                                                         -- add rbx, rsi
  rivet_step                                                         -- mov rax, rbx
  rivet_step (disch := (apply permits_inside read <;> bv_omega))    -- pop rbx
  rivet_step (disch := (apply permits_inside read <;> bv_omega))    -- ret
  exact Ensures.done (by
    simp [*, MachineState.returnAddress, BitVec.sub_add_cancel]
    constructor
    · rw [Memory.readBytes_storeBytes_disjoint] <;> bv_omega   -- the return address sits above the saved rbx
    · rw [Memory.readBytes_storeBytes_within] <;> simp)         -- pop reads back what push stored
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

## Rules that are easy to get wrong

- **Start your files with `module`.** Without it Lean can compute through the model's
  internals, which is slow and can exhaust its recursion limit.
- **Never unfold `permits`, `readBytes` or the operand functions.** Rewrite with
  `simp only [rivet]`, and use the laws: `permits_inside` and `permits_iff` for permissions,
  `Memory.readBytes_storeBytes_within` and `Memory.readBytes_storeBytes_disjoint` for a read
  after a store.
- **State permissions about the state the block starts from.** Side conditions come back
  stated over that state, so one hypothesis per region is enough.
- **Pick the law for each read yourself.** Giving both read laws to one
  `simp (disch := bv_omega)` applies the wrong one and reports an error.
- **Keep arithmetic small.** `bv_omega` slows down sharply as facts about words pile up.
  If a call is slow, state the fact as its own lemma and apply it.

## Sizing blocks

A block is one `Ensures` goal stepped from a single start state. The cost of a block grows
faster than its length, because everything it has done is carried to the end. Splitting is
what forgets: 320 instructions took 37 seconds as one block and 10 seconds as blocks of 80,
and below 80 there was nothing more to gain.

- **Start a new block about every 80 instructions,** and at every loop and call.
- **End a block with a postcondition that states only what later code needs:** where
  execution is, the registers that matter, the memory facts that matter.
- **Join blocks with `bind`:**

  ```lean
  refine (first_block regions s entry).bind fun t ⟨at_t, rbx_t, rsp_t, memory_t⟩ => ?_
  refine (second_block regions t at_t (by rw [rsp_t]; exact read)).consequence (fun _ h => h) ?_
  intro f ⟨at_f, rax_f⟩
  simp [*, MachineState.returnAddress]
  ```

  `bind` hands the second block the state `t` the first one ended in, with the first
  block's postcondition as the only facts about it. The second block's result is stated
  over `t`; `consequence` restates it over `s`.

- **Inside a block, name a checkpoint** with `rivet_step as t` whenever the context gets
  long. That returns the context to a fixed size; it does not shorten what the block
  remembers.
