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
    (write : permits (Image.writable ⟨sum, regions⟩) (s.registers .rsp - 8#64) 16 = true)
    (read : permits (Image.readable ⟨sum, regions⟩) (s.registers .rsp - 8#64) 16 = true) :
    Block ⟨sum, regions⟩ s
      -- all it changes: two registers and the slot below the stack pointer
      { registers := [.rax, .rsp],
        memory := [((s.registers .rsp).toNat - 8, (s.registers .rsp).toNat)] }
      (fun f =>
        f.status = .running s.returnAddress ∧
        f.registers .rax = s.registers .rdi + s.registers .rsi ∧
        f.registers .rsp = s.registers .rsp + 8#64) := by
  have room := (permits_iff.mp write).1
  rivet_step (disch := exact permits_inside write)       -- push rbx
  rivet_step                                             -- mov rbx, rdi
  rivet_step                                             -- add rbx, rsi
  rivet_step                                             -- mov rax, rbx
  rivet_step (disch := exact permits_inside read)        -- pop rbx
  rivet_step (disch := exact permits_inside read) as f   -- ret
  refine Block.done ⟨?_, by simp only [f_registers, rivet], by simp only [f_registers, rivet]⟩
  rw [f_status, m₁_def, Memory.readBytes_storeBytes_outside]   -- the return address sits above the saved rbx
  rfl
```

Each `rivet_step` executes one instruction and records what it changed. An instruction
that touches memory asks for a permission; `disch` proves it by naming the permission
the access falls in. The bounds a law asks for prove themselves with `rivet_arith`, which
handles arithmetic about words and numbers. `Block.done` ends the block once `Q` holds of
the current state, and checks the change against what the steps recorded: `rbx` is not in
it because `pop` reads back what `push` stored, and leaving out `rax` or the stack slot is
an error naming it.

To work on a real binary, generate the program instead of writing it by hand:

```sh
cargo run -p rivet-import -- ./prog --function sum --namespace Sum --output Sum.lean
```

That gives `Sum.entry`, `Sum.program`, `Sum.regions` for the binary's segments, and
`Sum.Loaded memory`, which says memory holds each segment's bytes.

## API

[API.md](API.md) lists everything a proof can use, by concept.
