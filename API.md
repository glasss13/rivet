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

- `rivet_call block args (as q)?` runs a block you proved. Give it the block's arguments up to
  its start state, which it takes from the goal. Each precondition is proved by reading back
  (below), with no arithmetic; one that is not is an error naming it, and you give it by name:
  `rivet_call copy a (room := by …)`. The proof goes on from the state the block ends in, with
  `q_post`, its postcondition, and `q_kept`, what it left alone, in scope (hidden without `as q`).
  A postcondition that is an `∨` is one way out per side, as a branch is: one goal for each, in
  order, with that side as `q_post`.
- `exact Block.done` ends the block at the current state. It proves `Q`, and that every store went
  into a region `c` lists, by reading back, with no arithmetic. `Block.done proof` takes your proof
  of `Q` instead: `Block.done ⟨by rivet_close, by rivet_arith only [bound]⟩`.
- `Block.loop invariant measure holds fun current kept inv => …`: a loop whose head is `t`, as a
  block of its own, `Block image t c exit`, where `holds : invariant t`. Each pass goes on from a
  `current` in the invariant, and ends back in it with a smaller `measure`, or in `exit`.

```lean
theorem copy (s : MachineState) (pre : AtCopy a s) (dest : (output a).Has (s.registers .rdi) 8) :
    Block (image a) s { registers := [.rcx, .r8, .r11], memory := [output a] }
      (fun t => t.status = .running 0x4017b3) := by
  refine Block.loop (AtCopy a) (fun c => (s.registers .rdi).toNat - (c.registers .r8).toNat) pre
    fun c kept inv => ?_
  -- step; each exit: `exact Block.done …`
```

## Reading back

Rivet reads every value back to the block's start. `rivet_known` closes a goal that, read that way,
is a hypothesis or has two equal sides; `Block.done` and `rivet_call` close their goals with it.
`rivet_close` is `rivet_known`, then `rivet_arith` on each part left: your arithmetic, on your
goal, over everything in scope. Rivet sees through an `abbrev` and a record's fields (a record is
a `structure` in `Prop`), never a `def`.

What is read back, each step a lookup and none of them arithmetic:

- a register, through each step that did not write it and each nested block whose change does
  not list it;
- a read (`readBytes m p n`; a byte is `n = 1`) that is placed: `r.Has p n` is a hypothesis as
  written, or `p` is a literal place. It passes each store placed in a region apart from `r`, and
  each nested block whose change lists only regions apart from `r`. At a store into `r` it gives
  the value stored (or its low bytes) when it is at the store's pointer as written, and passes
  the store when both are a literal number of bytes off one base (`rsp + 56` and `rsp - 8`).
  Anything else stops there, and the error states the two facts to choose from;
- a goal `r.Same s.memory t.memory`, the same way: every store since `s` is placed in a region
  apart from `r`, and every nested block's change lists only such regions.

A read that is not placed is not read back, and the error names the `Has` to state. A fact over
many addresses (a `∀`) is carried by a lemma you prove once for its predicate, from `r.Same`:

```lean
theorem Table16.carry (same : (table a).Same m m') (t : Table16 m T b) : Table16 m' T b
-- at each call:
exact Block.done ⟨by rivet_known, table16.carry (by rivet_known)⟩
```

A goal is taken apart (`∧`, `∀`, records; of `∨`, either side), and a part closes when it is a
hypothesis or a part of one (a `∀` one applies when its premises are hypotheses), or its two sides
are the same. A place (`r.Has p n`, `r.At o p`), a permission (`image.Reads r`) and `r.Apart r'`
close by the lookups under Memory. For `∃`, give the witness. The status and the flags are not
read back through a nested block: a change says nothing of them, so the block's postcondition must.

An error shows each part that did not close, as asked and as read back, and where each read
stopped: at a store (named by its instruction and address) or a nested block, with the region it
is not known apart from.

## Stepping

`rivet_step (disch := tac)? (as t)? (if h)?` executes the instruction at the current state's
`status = .running address` through its contract.

- **Facts.** The new state gets one fact per field: `status`, `registers`, `memory`,
  `signFlag`, `zeroFlag`, `carryFlag`, `overflowFlag`, `xmmRegisters`. They are stated over the
  block's start state, or over the end of the last nested block for what that block changed. The
  previous state is dropped, unless one of your hypotheses mentions it.
- **Names.** `as t` names the new state and its facts `t_status`, `t_registers`, …. Unnamed,
  they are hidden. Name a state to state a fact about it.
- **Memory.** Each store makes `mₙ` with `mₙ_def : mₙ = mₙ₋₁.storeBytes …`.
- **Branches.** A conditional jump gives two goals, `taken` and `fallthrough`. `if h` names the
  condition `h` in both (negated in `fallthrough`); otherwise it is hidden.
- **Return.** After `ret` the status is `.running (readBytes m rsp 8)`: the 8 bytes at `rsp`
  before the return.
- **Places.** A memory access asks where its pointer is: `r.Has pointer size`, for a region the
  image grants. `rivet_step` finds it as a hypothesis as written, or as a literal place (below);
  otherwise `disch` proves it: `rivet_step (disch := exact left.first positive)`, and the place is
  kept as a hypothesis (`t_place0`), so that reading back finds it. An access
  that is not placed is an error at that step.
- **Other side conditions** (operand checks) are stated over the block's start state. `rivet_step`
  tries `rfl`, `decide` and `assumption`, then `disch`; one left open is your goal.
- Your own hypotheses are never rewritten.

## Arithmetic

A step's facts are about words (`rdi + rax`, `rax < rdx`, `rsp - 8#64`); bounds and invariants are
plain numbers over `x.toNat`. `rivet_arith [f₁, f₂, …]` proves goals that mix the two, with Lean's
`lia`, from the hypotheses in scope and the listed facts, with the registers of the goal and of
those facts read back first.

- A fact is a statement about the goal's terms. A listed record (`inv`) is given field by field;
  `lia` does not look inside one in scope. A general fact (`∀ x, …`) is ignored: give it its
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
place you prove. A read is placed in a region. A fact moves across anything that does not name its
region. Rivet compares names and literal offsets and never searches.

The model is flat, and so is what a theorem means: `Memory` is a byte per 64-bit address, and
`Memory.storeBytes memory base length bytes` writes the addresses whose value lies in
`[base.toNat, base.toNat + length)`. `readBytes memory address size` is the one way to read;
`readBytes` and `littleEndianAt` are closed: use the laws.

- `Region` (`base`, `length`, `readable`, `writable`, `fits : base + length ≤ 2^64`), `Image`
  (`program`, `regions`). Name each region of the spec, and each part of one your proof tells
  apart, with an `abbrev`: `abbrev saved (a) : Region := (stack a).part 16 128`.
- `r.Same m m'`: the two memories agree on every byte of `r`. `same.read placed`: a read placed
  in `r` is the same in both. Statements always read the real memory.
- `r.Has pointer size`: `size` bytes at `pointer` lie in `r` (a record of two bounds; prove it with
  your arithmetic). `placed.first le` and `placed.part start finish`: a place covers its parts.
- `r.At offset pointer`: `pointer` is `offset` bytes into `r`. State it once for a register that
  holds a frame: `(stack a).At 8 (s.registers .rsp)`. A pointer that is such a register plus or
  minus literals is a *literal place*: Rivet adds the literals and finds the named part it lies in.
- `r.Apart r'`, and `image.Reads r`, `image.Writes r`.
- `image.Layout [r₁, r₂, …]`: the image grants each region what the region states, and they are
  pairwise apart. Prove it once, from the spec's assumption, and carry it as a hypothesis of each
  block. `Image.grants_of_mem` and `Image.Grants.part` prove the grants.

Lookups. `image.Reads r`, `image.Writes r` and `r.Apart r'` are found as a hypothesis as written,
or from a layout in scope that lists the regions. A block that takes its regions as arguments
states them as hypotheses: `(writes : image.Writes dst) (apart : dst.Apart slot)`.

Laws, for what the read-back stops at. Every bound is an argument you give.

- `Memory.readBytes_storeBytes_inside` and `_outside` (a read inside a store reads the stored
  bytes; one outside it is unchanged), `readBytes_littleEndianAt value offset`, and
  `placed.readBytes_stored`: a read at a store's pointer reads the value stored.
- `readBytes_succ`: a read in terms of its bytes. A read of known bytes:
  `simp only [readBytes_succ, BitVec.of_length_zero]; decide`.

## What a theorem means

`Block` is defined from the model: `step image state flags` runs one instruction, and
`execute image n state choices` runs `n` of them with one value of the undefined flags per step
(`FlagChoices`). Proofs never mention them; they are what a theorem's meaning rests on.

What a proof does not cover: the decoder (instructions come from the importer and iced-x86), the
CPU (the model is tested against hardware, not proved equal to it), flags other than ZF, CF, SF
and OF, instructions outside the supported subset, and concurrency.

## Importer and checker

- `cargo run -p rivet-import -- ./prog --function f --namespace F --output F.lean` writes
  `F.entry`, `F.program`, `F.regions` (the binary's segments) and `F.Loaded memory` (memory holds
  the segments' bytes).
- `cargo run -p rivet-check -- --cases 1000` tests the model against the CPU.
