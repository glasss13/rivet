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

## Contracts

- `Ensures image s Q`: from state `s`, for every value of the undefined flags, execution
  reaches a state satisfying `Q` in finitely many steps.
- `Ensures.done`: `Q s` proves `Ensures image s Q`.
- `Ensures.bind`: one contract, then a continuation from every state it can end in.
- `Ensures.consequence`: weakens the postcondition.
- `Ensures.loop invariant measure holds body`: a loop. `body` starts from any state in the
  invariant and ends either back in it with a smaller `measure`, or in the postcondition.
- `Ensures.preserves_unwritable`: adds to a contract that memory no region may write is
  unchanged.

Joining two blocks:

```lean
refine (first_block regions s entry).bind fun t post => ?_
refine (second_block regions t post.status).consequence ?_
```

A loop whose head is `0x2000`:

```lean
refine Ensures.loop (fun c => c.status = .running 0x2000)
  (fun c => (c.registers .rcx).toNat) entry fun c at_head => ?_
-- each exit: `Ensures.done (.inl ⟨…, smaller⟩)` back to the head, or `Ensures.done (.inr …)`
```

## Stepping

`rivet_step (disch := tac)? (as t)? (if h)? (tracking [field, …])?` executes the
instruction at the current state's `status = .running address` through its contract.

- **Facts.** The new state gets one fact per field: `status`, `registers`, `memory`,
  `signFlag`, `zeroFlag`, `carryFlag`, `xmmRegisters`. `tracking [...]` keeps only those
  listed.
- **Names.** An unnamed state's facts are hidden. `as t` names the state and its facts
  `t_status`, `t_registers`, … (the state's name, `_`, the field).
- **Checkpoints.** `as t` also restates the facts over the block's start state and drops
  the unnamed states before it. At the next checkpoint, `t`'s facts are used and removed;
  `t` itself stays while one of your hypotheses mentions it.
- **Memory.** Each store makes `mₙ` with `mₙ_def : mₙ = mₙ₋₁.storeBytes …`, and later facts
  mention `mₙ`. Expand with `rw [m₂_def]`. A checkpoint removes a name nothing mentions.
- **Branches.** A conditional jump gives two goals, `taken` and `fallthrough`. `if h` names
  the condition `h` in both (negated in `fallthrough`); otherwise it is hidden.
- **Return.** After `ret` the status is `.running (readBytes m rsp 8)`: the 8 bytes at `rsp`
  before the return.
- **Side conditions** (permissions, operand checks) are stated over the block's start
  state, so one hypothesis per region proves them. `rivet_step` tries `rfl`, `decide` and
  `assumption`, then `disch`, or `simp [*, rivet]` without one. A `disch` that fails is an
  error at that step, showing the goal it saw. Anything else stays open after the main goal.
- Your own hypotheses are never rewritten. A checkpoint that cannot restate a fact is an
  error naming the field.

`rivet_fetch` proves `program.fetch address = some instruction` for a concrete program.

## Restricting a tactic to chosen facts

`with_only [f₁, f₂, …] => tac` closes the goal with `tac`, which sees the goal, the
variables and the listed facts, and no other hypothesis.

- A fact is any term: a hypothesis, a field of a structure (`inv.bound`), a step's fact
  (`t_registers`), `‹_›`. One given by name keeps the last part of its name.
- `tac` gets a fresh `maxHeartbeats` budget. `grind` and `simp` stop at it; `bv_omega` does
  not.
- `tac` must close the goal; leftover goals are an error.

State bounds in plain numbers (`x.toNat`) and close them with `omega`. It ignores facts about
words, so a large context costs it nothing and it needs no `with_only`. `grind` and
`bv_omega` read every hypothesis in scope, and their cost grows with how many facts about
words are there; `with_only [...] => grind` keeps them to the facts the goal needs:

```lean
rivet_step (disch := exact Image.permits_writable stackMember rfl (by omega))
exact Ensures.done (by with_only [t_registers, inv.bound] => grind)
```

## Machine model

- `MachineState`: `registers`, `xmmRegisters`, `signFlag`, `zeroFlag`, `carryFlag`, `memory`,
  `status`.
- `ExecutionStatus`: `running address` or `fault`; `.isRunning`.
- `MachineState.write`: sets a register. `MachineState.writeMemory`: stores a value
  little-endian.
- `MachineState.returnAddress`: the 8 bytes at `rsp`.
- `FlagValues`, `FlagChoices` (one value of the undefined flags per step), `FlagChoices.drop`.
- `Condition.holds`: whether a jump condition holds in a state.
- `MachineState.readOperand`, `writeOperand`, `canRead`, `canWrite`, `Address.evaluate`:
  operands and addresses. Closed: rewrite them with `simp only [rivet]`.
- `step`, `execute`: one instruction, and a number of them. Closed: use the laws.

## Programs and instructions

- `Reg`, `Reg32`, `Reg16`, `Reg8` (with `.parent`), `Xmm`, `Width` (`.bytes`, `.bits`),
  `Scale` (`.value`), `Address`, `Operand` (`.width`).
- `Op`, `BinaryOp`, `ShiftOp`, `Condition`, `XmmMove`, `Instruction`, `Program`,
  `Program.fetch`.
- `validMove`, `validBinary`, `validConditionalMove`, `validImul`, `validShift`: operand
  checks, side conditions of the contracts.
- `InstructionAt program address length op`: the evidence a contract takes.
- `Program.FetchesFrom program suffix address`, `.skip`: fetching from a suffix.

One contract per instruction, applied by `rivet_step`: `move`, `movzx`, `movsxd`, `lea`,
`add`, `sub`, `sbb`, `compare`, `test`, `bitwise_and`, `bitwise_or`, `bitwise_xor`,
`bitwise_not`, `imul`, `shift`, `inc`, `dec`, `setcc`, `cmovcc`, `push`, `pop`, `call`,
`return_`, `jump`, `branch`, `nop`, `movd`, `pshufd`, `load_xmm`, `store_xmm`.

## Memory

- `Memory`: a byte per 64-bit address. `Memory.storeBytes memory base length bytes`: writes the
  addresses whose value lies in `[base.toNat, base.toNat + length)`.
- `readBytes memory address size`, `littleEndianAt value address`, `permits`: closed; never
  unfold them, use the laws below.
- `Region` (`base`, `length`, `readable`, `writable`), `Image` (`program`, `regions`),
  `Image.readable`, `Image.writable`. A region holds the addresses whose value lies in
  `[base.toNat, base.toNat + length)` (`Region.Contains`); it never wraps.
- `region.Covers address size`: the region holds `[address.toNat, address.toNat + size)`, and
  that range ends at or below 2^64. It unfolds for `omega`. For a region written out as a
  structure, `simp only [Region.Covers]` first exposes its fields.

Laws. Ranges are intervals of `toNat` values, empty ones included, and lengths are numbers of
bytes. An access ending past 2^64 would wrap around: the machine faults on it, and the laws
about reads ask for `address.toNat + size ≤ 2^64`.

- `Image.permits_readable`, `Image.permits_writable`: an access a region covers is permitted,
  given the region is in the image and grants the permission. Prove membership by `simp` with
  the region list's definitions unfolded.
- `permits_iff`: what a permission means, address by address. `permits_inside`: a permission
  covers any part of its range.
- `Region.Covers.toNat_add`: `(p + BitVec.ofNat 64 k).toNat = p.toNat + k` when the region
  covers more than `k` bytes from `p`. To place an address such as `c + r - 16` relative to a
  covered `s + r - 16`, rewrite it as `(s + r - 16) + (c - s)` with `grind` first.
- `Memory.readBytes_storeBytes_inside`: a read inside a store reads the stored bytes.
- `Memory.readBytes_storeBytes_outside`, `Memory.read_storeBytes_outside`: a read or a byte
  outside a store is unchanged.
- `readBytes_congr`: two memories that agree on a range read the same there.
- `readBytes_succ`: a read in terms of its bytes. A read of known bytes:
  `simp only [readBytes_succ, BitVec.of_length_zero]; decide`. `readBytes_one`: one byte.
- `readBytes_littleEndianAt`, `readBytes_littleEndianAt_add`, `littleEndianAt_add`,
  `littleEndianAt_self`: reading back a stored value, or part of it.
- `Memory.SameOutside before after footprint`: memory changed only inside `footprint`;
  `refl`, `trans`, `mono`, `storeBytes` (extend across a store inside the footprint),
  `readBytes` (a read outside it is unchanged).

## Registers

- `MachineState.SameRegistersOutside before after written`: every register not in `written`
  is unchanged; `refl`, `trans`, `mono`. Applied to a register:
  `h .rsi (by decide) : after.registers .rsi = before.registers .rsi`.

## The `rivet` simp set

`simp only [rivet]` rewrites operand reads and writes, register parts and addresses into
point reads of registers, and puts facts in one spelling. It contains:

- `MachineState.canRead_*`, `canWrite_*`, `readOperand_*`, `writeOperand_*`: one per operand
  kind.
- `Address.evaluate_*`: one per address shape. `Reg8.parent`, `Reg16.parent`, `Reg32.parent`,
  `Width.bytes`.
- Spelling: `le_and_ne_iff_lt`, `lt_or_eq_iff_le`, `sub_ofNat_sub_ofNat`,
  `add_ofNat_add_ofNat`, `add_ofNat_sub_ofNat_of_le`, `add_ofNat_sub_ofNat_of_ge`,
  `sub_ofNat_add_ofNat_of_le`, `sub_ofNat_add_ofNat_of_ge`, `read_low_byte`,
  `write_low_byte_twice`, `read_low_word`, `write_low_word_twice`, and some of Lean's
  `BitVec` lemmas.

## Importer and checker

- `cargo run -p rivet-import -- ./prog --function f --namespace F --output F.lean` writes
  `F.entry`, `F.program`, `F.regions` (the binary's segments) and `F.Loaded memory` (memory
  holds the segments' bytes).
- `cargo run -p rivet-check -- --cases 1000` tests the model against the CPU.
