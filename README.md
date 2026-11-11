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

## Rules that are easy to get wrong

- **Start your files with `module`.** Without it Lean can compute through the model's
  internals, which is slow and can exhaust its recursion limit.
- **Never unfold `permits`, `readBytes` or the operand functions.** Rewrite with
  `simp only [rivet]`, and use the laws: `permits_inside` and `permits_iff` for permissions,
  `Memory.readBytes_storeBytes_within` and `Memory.readBytes_storeBytes_disjoint` for a read
  after a store, `readBytes_succ` for a read of bytes you know, as in
  `simp only [readBytes_succ, BitVec.of_length_zero]; decide`. A store names the memory it
  leaves, `m₁`, `m₂`, …; rewrite with that fact first, as in `rw [‹m₁ = _›]`.
- **State permissions about the state the block starts from.** Side conditions come back
  stated over that state, so one hypothesis per region is enough.
- **Keep an invariant or postcondition whole.** State it as a structure, bind it as one
  hypothesis, and name the fields a line uses: `grind [inv.bound, inv.rsp]`. Arithmetic
  tactics read every hypothesis in scope; a whole structure keeps its fields out of their
  way until named.

## Sizing blocks

A block is one `Ensures` goal stepped from a single start state. The cost of a block grows
faster than its length, because everything it has done is carried to the end. Splitting is
what forgets: 320 instructions took 37 seconds as one block and 10 seconds as blocks of 80,
and below 80 there was nothing more to gain.

- **Start a new block about every 80 instructions,** and at every loop and call.
- **End a block with a postcondition that states only what later code needs:** where
  execution is, the registers that matter, the memory facts that matter.
- **Say which registers a block writes,** not which it keeps:
  `s.SameRegistersOutside t [.rax, .rbx, .rsp]`, proved at the end of the block by
  `simp +contextual [MachineState.SameRegistersOutside, *]`. A loop invariant states the
  same about the loop's entry state, `s₀.SameRegistersOutside s loopWrites`. It crosses a
  block with `inv.trans (block.mono (by decide))`, and `rw [inv _ (by decide)]` turns a
  register the loop never writes into its value at `s₀`.
- **Join blocks with `bind`:**

  ```lean
  refine (first_block regions s entry write).bind fun t summed => ?_
  refine (second_block regions t summed.status (by rw [summed.rsp]; exact read)).consequence ?_
  intro f restored
  simp [restored.status, restored.rax, restored.rbx, restored.rsp,
    summed.rax, summed.rsp, summed.saved, summed.ret, BitVec.sub_add_cancel]
  grind
  ```

  `bind` hands the second block the state `t` the first one ended in, with the first
  block's postcondition `summed` as the only fact about it. The second block's postcondition is
  stated over `t`; `consequence` turns it into the one the theorem promises about `s`.

- **Inside a block, name a checkpoint** with `rivet_step as t` whenever the context gets
  long. That returns the context to a fixed size plus one line per store; it does not
  shorten what the block remembers.

## Loops

`Ensures.loop` takes an invariant that holds at the loop head and a measure. The body must
end either back in the invariant with a smaller measure, or in the postcondition.

```lean
-- loop: dec rcx · jne loop
def countdown : Program :=
  [⟨0x2000, 3, .dec .rcx⟩,
   ⟨0x2003, 2, .jcc .notEqual 0x2000⟩]

theorem countdown_exits (regions : List Region) (s : MachineState)
    (entry : s.status = .running 0x2000) :
    Ensures ⟨countdown, regions⟩ s (fun f =>
      f.status = .running 0x2005 ∧ f.registers .rcx = 0#64) := by
  refine Ensures.loop (fun c => c.status = .running 0x2000)
    (fun c => (c.registers .rcx - 1#64).toNat) entry fun c at_head => ?_
  rivet_step                                           -- dec rcx
  rivet_step                                           -- jne loop
  · exact Ensures.done (.inl (by simp [*]; grind))     -- taken: at the head, one fewer to go
  · exact Ensures.done (.inr (by simp [*]))            -- fell through: rcx is zero
```
