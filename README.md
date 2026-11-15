# Rivet

A Lean 4 library for proving things about x86-64 machine code. You import a compiled
function, state what it should do, and step through its instructions until Lean accepts
the proof.

```sh
lake build
```

## What a theorem says

`Block image s c Q` means: from the machine state `s`, and for every value the CPU might
leave in its undefined flags, execution reaches a state in finitely many steps that
satisfies `Q` and is `s` except for the change `c`: every register and every byte of memory
that `c` does not list is as it was. What the start state must satisfy is stated as ordinary
hypotheses about `s`. A fault is permanent, so a `Q` that requires `status = .running …`
also proves that nothing faulted on the way.

What a proof does not cover:

- The decoder. Instructions come from the importer and iced-x86, not from Lean.
- The CPU. The model is tested against real hardware (`cargo run -p rivet-check -- --cases 1000`),
  not proved equal to it.
- Flags other than ZF, CF, SF and OF, instructions outside the supported subset, and concurrency.

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

-- the body, a block of its own: from 0x1001 it changes rax and rbx
theorem add_body (regions : List Region) (s : MachineState) (entry : s.status = .running 0x1001) :
    Block ⟨sum, regions⟩ s { registers := [.rax, .rbx] }
      (fun t => t.status = .running 0x100a ∧ t.registers .rax = s.registers .rdi + s.registers .rsi) := by
  rivet_step                                           -- mov rbx, rdi
  rivet_step                                           -- add rbx, rsi
  rivet_step                                           -- mov rax, rbx
  exact Block.done

theorem sum_correct (regions : List Region) (stack : Region) (s : MachineState)
    (entry : s.status = .running 0x1000)
    (reads : Image.Reads ⟨sum, regions⟩ stack) (writes : Image.Writes ⟨sum, regions⟩ stack)
    -- the caller's promise: 16 bytes of stack, the slot `push` uses and the return address
    (frame : stack.Has (s.registers .rsp - 8#64) 16) :
    -- all it changes: two registers and the stack
    Block ⟨sum, regions⟩ s { registers := [.rax, .rsp], memory := [stack] }
      (fun f =>
        f.status = .running s.returnAddress ∧
        f.registers .rax = s.registers .rdi + s.registers .rsi ∧
        f.registers .rsp = s.registers .rsp + 8#64) := by
  rivet_step                     -- push rbx
  rivet_call add_body regions    -- the body
  rivet_step                     -- pop rbx
  rivet_step                     -- ret
  exact Block.done
```

Each `rivet_step` executes one instruction. Memory is named regions, as the state is named
registers: an instruction that touches memory must be placed in a region the image grants, here by
`frame`, which places the 8 bytes `push` writes and the 8 bytes `ret` reads.

Rivet reads every value back to the block's start: a register through the steps that did not
write it, memory through the stores into regions apart from it, and both through a nested block
that left them alone. A goal closes when, read that way, it is one of your hypotheses or its two
sides are the same. Rivet never searches and starts no arithmetic; what it cannot read back is
an error that says what to prove.

`Block.done` ends the block that way. It proves `Q` of the current state, and it proves the
change: every register the change does not list is as it was, and every store went into a region
it lists. `rbx` is not listed, although the body changed it, because `pop` reads back what `push`
stored. The return address is the same kind of read: 8 bytes past the saved `rbx`, so the push
did not touch it. Two pointers a literal distance apart, like `rsp` and `rsp - 8`, are compared by
that distance; any others are apart only when their regions are.

`rivet_call` runs a block you proved as a nested block. It starts it at the current state,
proves its preconditions the same way (`add_body` asks only for its entry address), and goes on
from the state it ends in, with its postcondition and what it left alone. A precondition it
cannot prove is an error at the call naming it; give it by name, `rivet_call f a (room := …)`.

To work on a real binary, generate the program instead of writing it by hand:

```sh
cargo run -p rivet-import -- ./prog --function sum --namespace Sum --output Sum.lean
```

That gives `Sum.entry`, `Sum.program`, a region `Sum.region_<address>` for each of the binary's
segments, `Sum.regions`, and `Sum.Loaded memory`, which says memory is the segment's bytes on each
segment's region.

## API

[API.md](API.md) lists everything a proof can use, by concept.
