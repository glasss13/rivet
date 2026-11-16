# Rivet API

Everything a proof can use, by concept. All names are in namespace `Rivet`. Start each proof
file with

```lean
module
import Rivet
open Rivet
```

Without `module`, Lean can compute through the model's internals, which is slow and can
exhaust its recursion limit.

## Blocks

- `Block image s c Q`: from state `s`, for every value of the undefined flags, execution
  reaches in finitely many steps a state `t` that satisfies `Q t` and is `s` except for the
  change `c`. It is the only kind of contract: a function, a loop, a stretch of code and each
  instruction are all blocks.
- `Changes`: what a block may change. `registers` is a list of registers; `memory` is a list of
  regions (`memory := [output a, scratch a]`; a region stands for its range `(low, high)`). Both
  default to empty.
- `t.Except s c`: every register outside `c.registers` and every read outside `c.memory` is the
  same in `t` as in `s`. Flags, vector registers and the status are not compared: state what you
  need of them in `Q`. It compares the end with the start, so a register the block saves and
  restores is not in the change. `kept.same`: the two memories are the `Same` on a region the change misses.

While you step through a block from `s`, the goal is `Block image s c Q t`: the same block, now
at the state `t` reached so far. The code in between runs as nested blocks: each instruction is
one, and so is any block you proved. Only the block's end is compared with its start, so a nested
block may change what the block keeps, if the code after it restores it.

- `rivet_call block args` runs a block you proved: `rivet_call copy a`, `rivet_call copy a as q`,
  `rivet_call copy a (room := proof) as q`. Give it the block's arguments up to its start state,
  which it takes from the goal. Each precondition is proved as `rivet_known` does; one that is not
  is an error naming it, and you give it by name. The proof goes on from the state the block ends
  in, with `q_post`, its postcondition, and `q_kept`, what it left alone, in scope (hidden without
  `as q`). A postcondition that is an `∨` is one way out per side, as a branch is: one goal for
  each, in order, with that side as `q_post`.
- `exact Block.done` ends the block at the current state. It proves `Q`, and that every store went
  into a region `c` lists, as `rivet_known` does. `Block.done proof` takes your proof of `Q`
  instead: `Block.done ⟨by rivet_known, by rivet_arith only [bound]⟩`.
- `Block.loop invariant measure holds body`: a loop whose head is `t`, as a block of its own.

```lean
theorem Block.loop (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
    (body : ∀ current, current.Except t c → invariant current →
      Block image t c (fun next => invariant next ∧ measure next < measure current ∨ exit next) current) :
    Block image t c exit
```

A pass goes on from `current`. Where it jumps back, prove the invariant again with a smaller
measure, `Block.done (Or.inl ⟨⟨…⟩, …⟩)`; where it leaves, prove `exit`, `Block.done (Or.inr ⟨…⟩)`.
Registers the change does not list read back to `t` through `kept`.

```lean
-- mov [rdi], sil · inc rdi · dec rdx · jne 0x1000
structure Filling (dst : Region) (s t : MachineState) : Prop where
  status : t.status = .running 0x1000
  left : dst.Has (t.registers .rdi) (t.registers .rdx).toNat
  positive : 0 < (t.registers .rdx).toNat

theorem fill (dst : Region) (s : MachineState) (writes : image.Writes dst) (start : Filling dst s s) :
    Block image s { registers := [.rdi, .rdx], memory := [dst] } (fun t => t.status = .running 0x100b) := by
  refine Block.loop (Filling dst s) (fun t => (t.registers .rdx).toNat) start fun c kept inv => ?_
  have fits := dst.fits
  have byte : dst.Has (c.registers .rdi) 1 := inv.left.first inv.positive   -- the place of this pass's store
  rivet_step
  rivet_step
  rivet_step
  rivet_step if more
  · exact Block.done (Or.inl ⟨⟨by rivet_known,
      ⟨by rivet_arith only [inv, fits, more], by rivet_arith only [inv, fits, more]⟩,
      by rivet_arith only [inv, more]⟩, by rivet_arith only [inv]⟩)
  · exact Block.done (Or.inr (by rivet_known))
```

## Reading back

Rivet reads every value back to the block's start. `rivet_known` closes a goal that, read that way,
is a hypothesis or has two equal sides; `Block.done` and `rivet_call` close their goals with it.
There are two closing tactics: `rivet_known`, which starts no arithmetic and never searches, and
`rivet_arith` (below), which is yours. Rivet sees through an `abbrev` and a record's fields (a
record is a `structure` in `Prop`), never a `def`. Every lookup does: a place, a permission,
apartness, and the current address. A lookup reads your hypotheses back as it reads the goal, so a
place stated over a named state, `buf.Has (u.registers .rdi) 8`, places what the step writes.

What is read back, each step a lookup and none of them arithmetic:

- a register, through each step that did not write it and each nested block whose change does
  not list it;
- a read (`readBytes m p n`; a byte is `n = 1`) that is placed, by the rule under Memory: past a
  store or a nested block by its region. Where it stops, the error states what to prove;
- a goal `r.Same s.memory t.memory`: every store since `s` is placed in a region apart from `r`,
  and every nested block's change lists only such regions.

A fact over many addresses (a `∀`) is carried by a lemma you prove once for its predicate, from
`r.Same`:

```lean
theorem Table16.carry (same : (table a).Same m m') (t : Table16 m T b) : Table16 m' T b
-- at each call:
exact Block.done ⟨by rivet_known, table16.carry (by rivet_known)⟩
```

A goal is taken apart (`∧`, `∀`, records; of `∨`, either side), and a part closes when it is a
hypothesis or a part of one (a `∀` one applies when its premises are hypotheses), or its two sides
are the same (`x ≤ x` too). A place (`r.Has p n`), a permission (`image.Reads r`) and `r.Apart r'`
close by the lookups under Memory. For `∃`, give the witness. The status and the flags are not
read back through a nested block: a change says nothing of them, so the block's postcondition must.

An error shows each part that did not close, as asked and as read back, and where each read
stopped: at a store (named by its instruction and address) or a nested block, and what to prove there.

## Stepping

`rivet_step` executes the instruction at the current state's `status = .running address` through
its contract. It is written `rivet_step`, `rivet_step as t`, `rivet_step if h` or
`rivet_step as t if h`.

- **Facts.** The new state gets one fact per field: `status`, `registers`, `memory`,
  `signFlag`, `zeroFlag`, `carryFlag`, `overflowFlag`, `xmmRegisters`. They are stated over the
  block's start state, or over the end of the last nested block (in a loop, `current`) for what
  that block changed. The previous state is dropped, unless one of your hypotheses mentions it.
- **Names.** `as t` names the new state and its facts `t_status`, `t_registers`, `t_memory`, ….
  Unnamed, they are hidden. Name a state to state a fact about it.
- **Memory.** Each store makes a memory `mₙ` (`m₁`, `m₂`, …; named whether or not the state is),
  with `mₙ_def : mₙ = m.storeBytes p n (littleEndianAt v p)`: `m` the memory before, `p` the
  pointer, `n` the size as a literal, `v` the value. For `mov [rdi], rsi` from `s`:
  `m₁_def : m₁ = s.memory.storeBytes (s.registers .rdi) 8 (littleEndianAt (s.registers .rsi) (s.registers .rdi))`,
  and `t_memory : t.memory = m₁`.
- **Branches.** A conditional jump gives two goals, `taken` and `fallthrough`. `if h` names the
  condition `h` in both (negated in `fallthrough`); otherwise it is hidden. It is a statement
  about words, such as `¬x - 1#64 = 0#64`, not about a flag.
- **Return.** After `ret` the status is `.running (readBytes m rsp 8)`: the 8 bytes at `rsp`
  before the return.
- **Places.** A memory access needs its place, `r.Has pointer size`, and the permission,
  `image.Reads r` or `image.Writes r`, in scope before the step (see Memory). An access that is
  not placed is an error at that step, which shows the `Has` to state, over the block's start; over
  a named state is the same.
- **Other side conditions** (operand checks) are stated over the block's start state. `rivet_step`
  tries `rfl`, `decide` and `assumption`; one left open is your goal.
- Your own hypotheses are never rewritten.

## Arithmetic

A step's facts are about words (`rdi + rax`, `rax < rdx`, `rsp - 8#64`); bounds and invariants are
plain numbers over `x.toNat`. `rivet_arith` proves goals that mix the two, with Lean's `lia`. It is
written `rivet_arith`, `rivet_arith [f₁, f₂]` (the hypotheses in scope and the listed facts) or
`rivet_arith only [f₁, f₂]` (the listed facts alone). It first reads the goal and those facts
back, registers and memory, as `rivet_known` does.

- A fact is a statement about the goal's terms. A listed record (`inv`) is given field by field,
  and a goal that is a record (`r.Has p n`) is proved field by field; `lia` does not look inside
  a record in scope. A general fact (`∀ x, …`) is ignored: give it its
  arguments (`lemma x`).
- It reads `+`, `-`, multiplication by a literal, comparisons, `toNat`, literals, `if`, `>>>`,
  `<<<`, `setWidth`, and `BitVec.ofNat w n` when `n < 2^w`. The contracts state `not` as
  `-x - 1` and `movsxd` as a sum with an `if`, in these terms.
- It has a fixed budget of 20000 heartbeats that `maxHeartbeats` does not change, and its work
  does not count against the declaration. When the budget runs out, or `lia` fails on a goal you
  believe true, give it only the facts the goal needs: `rivet_arith only [f₁, f₂, …]` hides every
  other hypothesis. Facts the goal does not need, such as `%` or `/` facts and large `∨`s, can
  keep `lia` from a proof it finds without them.
- A term it does not read, such as a mask, needs its meaning as an equation, proved through
  `toNat`. Not with `bv_decide`: its proofs depend on an axiom that trusts compiled code.

  ```lean
  have : x &&& 15#64 = x % 16#64 := by
    apply BitVec.eq_of_toNat_eq; simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  ```

- A goal that adds or subtracts a shifted value may need `grind`.
- Do not use `bv_omega`: it rewrites every fact about words in scope, can run for minutes, and
  ignores `maxHeartbeats`.

## Machine and programs

- `MachineState`: `registers`, `xmmRegisters`, `signFlag`, `zeroFlag`, `carryFlag`,
  `overflowFlag`, `memory`, `status`. `ExecutionStatus`: `running address` or `fault`.
  `MachineState.returnAddress`: the 8 bytes at `rsp`. `Condition.holds`: whether a jump condition
  holds in a state.
- `Reg`, `Reg32`, `Reg16`, `Reg8` (with `.parent`), `Xmm`, `Width`, `Address`, `Operand`, `Op`,
  `Instruction`, `Program`.

One contract per instruction, each a `Block` whose change is what the instruction writes:
`move`, `movzx`, `movsxd`, `lea`, `add`, `sub`, `sbb`, `compare`, `test`, `bitwise_and`,
`bitwise_or`, `bitwise_xor`, `bitwise_not`, `imul`, `mul`, `tzcnt`, `shift`, `inc`, `dec`,
`setcc`, `cmovcc`, `push`, `pop`, `call`, `return_`, `jump`, `branch`, `nop`, `movd`, `pshufd`,
`load_xmm`, `store_xmm`. `rivet_step` applies them; read one to see exactly what an instruction does.

## Memory

Memory is named regions, as the state is named registers. A step writes into one region, at a
place you prove. A fact about a region crosses anything that does not name it.

**The rule.** A read passes a store, or a nested block, when its region is apart from the store's,
or from every region the block's change lists. At a store into its own region, how the two
pointers lie is a goal for you. Rivet never searches.

- **A place** is a hypothesis `r.Has q n`: it places `q`. A read or an access that is not placed
  stops, and the error names the `Has` to state. A place whose size is not a literal places only
  itself: state the bytes you access, `have byte : dst.Has p 1 := left.first positive`.
- **Apart, and granted.** `r.Apart r'`, `image.Reads r` and `image.Writes r` are hypotheses as
  written. Put those every block needs in a record of your own and carry it.
- **Where a read stops,** the error states the goal: that the read is outside the store, for
  `Memory.readBytes_storeBytes_outside`, or where it is inside it, for `placed.readBytes_stored`.
  A place you need and do not have is `placed.part start finish`, from its two bounds.

**Evaluated for you.** When two pointers are the same expression plus or minus literals
(`rsp + 56#64` and `rsp - 8#64`; two literal addresses) and the sizes are literals, those goals
are numbers, and Rivet evaluates them instead of handing them over. So
`stack.Has (s.registers .rsp - 8#64) 16` places the 8 bytes at `rsp - 8` and the 8 at `rsp`; a
read at `rsp` passes a store of 8 bytes at `rsp - 8`; and a read inside a store is those bytes
of the value stored. This never crosses a nested block: a change lists regions, so what must
survive a call is in a region the callee does not list.

The model is flat, and so is what a theorem means: `Memory` is a byte per 64-bit address, and
`Memory.storeBytes memory base length bytes` writes the addresses whose value lies in
`[base.toNat, base.toNat + length)`. `readBytes memory address size` is the one way to read;
`readBytes` and `littleEndianAt` are closed: use the laws.

- `Region` (`base`, `length`, `readable`, `writable`), `Image` (`program`, `regions`). Name each
  region with an `abbrev`. `r.part offset length` is a region inside `r`:
  `abbrev saved (a) : Region := (stack a).part 16 128`.
- `r.Has pointer size`, `r.Apart r'`, `r.Same m m'` (the two memories agree on every byte of `r`),
  `image.Reads r`, `image.Writes r`. A block that takes its regions as arguments states them:
  `(writes : image.Writes dst) (apart : dst.Apart slot)`. Statements always read the real memory.

The laws, with their arguments. Bounds are numbers, so `rivet_arith` needs them as facts: a place's
two (`placed.start`, `placed.finish`) and its region's `r.fits`.

```lean
Region.fits (r : Region) : r.base + r.length ≤ 2^64
Region.Has.start (placed : r.Has pointer size) : r.base ≤ pointer.toNat
Region.Has.finish (placed : r.Has pointer size) : pointer.toNat + size ≤ r.base + r.length
-- a place from one you have: its first bytes, or any bytes inside it, by their bounds
Region.Has.first (placed : r.Has pointer size) (le : less ≤ size) : r.Has pointer less
Region.Has.part (placed : r.Has pointer size) (start : pointer.toNat ≤ inner.toNat)
  (finish : inner.toNat + less ≤ pointer.toNat + size) : r.Has inner less
-- where a read stops at a store into its own region
Memory.readBytes_storeBytes_outside (memory bytes : Memory)
  (outside : address.toNat + size ≤ base.toNat ∨ base.toNat + length ≤ address.toNat)
  (fits : address.toNat + size ≤ 2^64) :
  readBytes (memory.storeBytes base length bytes) address size = readBytes memory address size
Region.Has.readBytes_stored (placed : r.Has stored length) (offset : Nat)
  (start : pointer.toNat = stored.toNat + offset) (inside : offset + size ≤ length)
  (memory : Memory) (value : BitVec n) :
  readBytes (memory.storeBytes stored length (littleEndianAt value stored)) pointer size =
    value.extractLsb' (8 * offset) (8 * size)
-- a read placed in a region is the same in two memories that are the same on it
Region.Same.read (same : r.Same earlier later) (placed : r.Has pointer size) :
  readBytes earlier pointer size = readBytes later pointer size
-- a permission, from the image's list and for a part
Image.reads_of_mem (member : r ∈ image.regions) (readable : r.readable = true) : image.Reads r
Image.Reads.part (reads : image.Reads r) (offset length : Nat) (inside : offset + length ≤ r.length) :
  image.Reads (r.part offset length inside)
-- and the same two for `Writes`: `Image.writes_of_mem`, `Image.Writes.part`
readBytes_succ (memory : Memory) (address : BitVec 64) (size : Nat) :
  readBytes memory address (size + 1) = readBytes memory (address + 1#64) size ++ BitVec.ofNat 8 (memory address).val
```

`first` is kept beside `part`: it takes the fact you have (`left.first positive`), where `part`
would ask for two bounds. To use a law on a read of a later state, rewrite with the step's facts
first: `rw [t_memory, m₁_def, Memory.readBytes_storeBytes_outside _ _ (by …) (by …)]`. A read of
known bytes: `simp only [readBytes_succ, BitVec.of_length_zero]; decide`.

## What a theorem means

`Block` is defined from the model: `step image state flags` runs one instruction, and
`execute image n state choices` runs `n` of them with one value of the undefined flags per step
(`FlagChoices`). Proofs never mention them; they are what a theorem's meaning rests on.

What a proof does not cover: the decoder (instructions come from the importer and iced-x86), the
CPU (the model is tested against hardware, not proved equal to it), flags other than ZF, CF, SF
and OF, instructions outside the supported subset, and concurrency.

## Importer and checker

- `cargo run -p rivet-import -- ./prog --function f --namespace F --output F.lean` writes
  `F.entry`, `F.program`, `F.region_<a>` for the segment at `a`, `F.regions` (all of them), and
  `F.Loaded memory`: on each segment memory is the segment's bytes,
  `segment_<a> : F.region_<a>.Same F.segment_<a> memory`.
  A constant read from a segment needs its place and its value as facts:
  `have place : F.region_<a>.Has 0x403000#64 8 := ⟨by decide, by decide⟩`, then
  `have value : readBytes s.memory 0x403000#64 8 = 42#64 := by rw [← loaded.segment_<a>.read place]; …`
  with the known-bytes recipe under Memory.
- `cargo run -p rivet-check -- --cases 1000` tests the model against the CPU.
