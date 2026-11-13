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
- `Changes`: what a block may change. `registers` is a list of registers; `memory` is a list
  of ranges `(low, high)`, the addresses whose value lies in `[low, high)`. Both default to
  empty. A change may mention the block's start state, not a later one.
- `t.Except s c`: every register outside `c.registers` and every byte outside `c.memory` is the
  same in `t` as in `s`. Flags, vector registers and the status are not compared: state what you
  need of them in `Q`. It compares the end with the start, so a register the block saves and
  restores is not in the change. Its fields, `sameRegisters` and `sameMemory`, are for proofs by hand.

While you step through a block from `s`, the goal is `Block image s c Q t`: the same block, now
at the state `t` reached so far. The code in between runs as nested blocks: each instruction is
one, and so is any block you proved. Only the block's end is compared with its start, so a nested
block may change what the block keeps, if the code after it restores it.

- `rivet_call block args (as q)?` runs a block you proved. Give it the block's arguments up to
  its start state, which it takes from the goal. Each precondition is proved by reading back
  (below); one that is not is an error naming it, and you give it by name:
  `rivet_call copy a (room := by …)`. The proof goes on from the state the block ends in, with
  `q_post`, its postcondition, and `q_kept`, what it left alone, in scope (hidden without `as q`).
- `exact Block.done` ends the block at the current state. It proves `Q`, and that nothing outside
  `c` changed, by reading back. `Block.done proof` takes your proof of `Q` instead.
- `Block.loop invariant measure holds fun current kept inv => …`: a loop whose head is `t`, as a
  block of its own, `Block image t c exit`, where `holds : invariant t`. Each pass goes on from a
  `current` in the invariant, and ends back in it with a smaller `measure`, or in `exit`.
- `Block.then inner fun next kept post => …` is the law behind `rivet_call`.

```lean
def copied (a : Arguments) : Changes :=
  { registers := [.rcx, .r8, .r11], memory := [(a.output.toNat, a.output.toNat + a.size.toNat)] }

theorem copy (s : MachineState) (pre : AtCopy a s) (room : (s.registers .rdi).toNat + 8 ≤ …) :
    Block (image a) s (copied a) (fun t => t.status = .running 0x4017b3) := by
  refine Block.loop (AtCopy a) (fun c => (s.registers .rdi).toNat - (c.registers .r8).toNat) pre
    fun c kept inv => ?_
  -- step; each exit: `exact Block.done`
```

## Reading back

Rivet reads every value back to the block's start. A goal closes when, read that way, it follows
from what you know. `Block.done` and `rivet_call` close their goals this way; `rivet_close` does
it for any goal.

What is read back:

- a register, through each step that did not write it and each nested block whose change does
  not list it;
- memory (`readBytes m a n`, or a byte `m a`), through each store the read misses, each store
  that wrote all of it (giving the bytes stored), and each nested block whose change it misses.
  Each of these is a bound for `rivet_arith`;
- a definition or record of yours that takes a state or a memory. A statement (`Globals a t`) is
  taken apart into what it says; a value (`matchLength t`) is unfolded where `t` is a later state.
  Definitions that take neither are left alone: unfold them yourself, or state what they equal.

A goal is taken apart (`∧`, `∀`, your statements; of `∨`, either side), and a part closes when it
is a hypothesis or a part of one, its two sides are the same, or `rivet_arith` proves it from the
hypotheses in scope. For `∃`, give the witness: `Block.done ⟨status, 0, by rivet_close⟩`. The status
and the flags are not read back through a nested block: a change says nothing of them, so the
block's postcondition must.

An error shows each part that did not close, as asked and as read back, and where each read
stopped: at a store (named by its instruction and address) or a nested block it is not shown to
miss, with the bound `rivet_arith` could not show. That bound is the fact to add.

## Stepping

`rivet_step (disch := tac)? (as t)? (if h)?` executes the instruction at the current state's
`status = .running address` through its contract.

- **Facts.** The new state gets one fact per field: `status`, `registers`, `memory`,
  `signFlag`, `zeroFlag`, `carryFlag`, `xmmRegisters`. They are stated over the block's start
  state, or over the end of the last nested block for what that block changed. The previous
  state is dropped, unless one of your hypotheses mentions it.
- **Names.** `as t` names the new state and its facts `t_status`, `t_registers`, …. Unnamed,
  they are hidden. Name a state to state a fact about it.
- **Memory.** Each store makes `mₙ` with `mₙ_def : mₙ = mₙ₋₁.storeBytes …`.
- **Branches.** A conditional jump gives two goals, `taken` and `fallthrough`. `if h` names the
  condition `h` in both (negated in `fallthrough`); otherwise it is hidden.
- **Return.** After `ret` the status is `.running (readBytes m rsp 8)`: the 8 bytes at `rsp`
  before the return.
- **Side conditions** (permissions, operand checks) are stated over the block's start state, so
  one hypothesis per region proves them. `rivet_step` tries `rfl`, `decide` and `assumption`, then
  `disch`, or `simp` without one. A `disch` that fails is an error at that step, showing the goal
  it saw. Anything else stays open after the main goal.
- Your own hypotheses are never rewritten.

## Arithmetic

A step's facts are about words (`rdi + rax`, `rax < rdx`, `rsp - 8#64`); bounds and invariants are
plain numbers over `x.toNat`. `rivet_arith [f₁, f₂, …]` proves goals that mix the two, with Lean's
`lia`, from the hypotheses in scope and the listed facts, with the registers of the goal and of
those facts read back first.

- A fact is a statement about the goal's terms. `lia` does not look inside a structure, so list
  the fields a goal needs (`inv.bound`), and give a general lemma its arguments (`lemma x`).
- It reads `+`, `-`, multiplication by a literal, comparisons, `toNat`, literals, `if`, `>>>`,
  `<<<`, `setWidth`, and `BitVec.ofNat w n` when `n < 2^w`. The contracts state `not` as
  `-x - 1` and `movsxd` as a sum with an `if`, in these terms.
- It has a fixed budget of 20000 heartbeats that `maxHeartbeats` does not change, and its work
  does not count against the declaration. When the budget runs out, give it only the facts the
  goal needs: `rivet_arith only [f₁, f₂, …]` hides every other hypothesis.
- A term it does not read, such as a mask, needs its meaning as an equation, proved through
  `toNat`. Not with `bv_decide`: its proofs depend on an axiom that trusts compiled code.

  ```lean
  have : x &&& 15#64 = x % 16#64 := by
    apply BitVec.eq_of_toNat_eq; simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  ```

- A goal that adds or subtracts a shifted value may need `grind`.
- Goals about plain numbers alone: `omega`. Do not use `bv_omega`: it rewrites every fact about
  words in scope, can run for minutes, and ignores `maxHeartbeats`.

## Machine and programs

- `MachineState`: `registers`, `xmmRegisters`, `signFlag`, `zeroFlag`, `carryFlag`, `memory`,
  `status`. `ExecutionStatus`: `running address` or `fault`. `MachineState.returnAddress`: the 8
  bytes at `rsp`. `Condition.holds`: whether a jump condition holds in a state.
- `Reg`, `Reg32`, `Reg16`, `Reg8` (with `.parent`), `Xmm`, `Width`, `Address`, `Operand`, `Op`,
  `Instruction`, `Program`.

One contract per instruction, each a `Block` whose change is what the instruction writes:
`move`, `movzx`, `movsxd`, `lea`, `add`, `sub`, `sbb`, `compare`, `test`, `bitwise_and`,
`bitwise_or`, `bitwise_xor`, `bitwise_not`, `imul`, `shift`, `inc`, `dec`, `setcc`, `cmovcc`,
`push`, `pop`, `call`, `return_`, `jump`, `branch`, `nop`, `movd`, `pshufd`, `load_xmm`,
`store_xmm`. `rivet_step` applies them; read one to see exactly what an instruction does.

## Memory

Addresses the CPU computes and the values it moves are words (`BitVec 64`). Region bounds, sizes
and facts about ranges are plain numbers over `address.toNat`.

- `Memory`: a byte per 64-bit address. `Memory.storeBytes memory base length bytes`: writes the
  addresses whose value lies in `[base.toNat, base.toNat + length)`.
- `readBytes memory address size`, `littleEndianAt value address`, `permits`: closed; never
  unfold them, use the laws below.
- `Region` (`base`, `length`, `readable`, `writable`, `fits : base + length ≤ 2^64`), `Image`
  (`program`, `regions`), `Image.readable`, `Image.writable`. A region holds the addresses whose
  value lies in `[base, base + length)`. A region written with `{ … }` proves `fits` by `decide`.

Laws. A read of `size` bytes at `address` reads `address + i` as a word, so the laws about reads
ask for `address.toNat + size ≤ 2^64`. Every bound a law asks for defaults to `by rivet_arith`, so
a law takes only its other arguments (`exact Image.permits_writable member rfl`). `apply` and `rw`
try the defaults at once. A default that fails is an error at that term; give the bound yourself,
`(fits := by rivet_arith [region.fits])`, or keep it as a goal, `(fits := ?_)`.

- `Image.permits_readable`, `Image.permits_writable`: an access inside a region is permitted,
  given the region is in the image and grants the permission. Prove membership by `simp` with
  the region list's definitions unfolded.
- `permits_iff`: what a permission means, address by address. `permits_inside`: a permission
  covers any part of its range.
- For a read the read-back stops at: `Memory.readBytes_storeBytes_inside` and `_outside` (a read
  inside a store reads the stored bytes; one outside it is unchanged), `readBytes_littleEndianAt`
  and `_add` (a stored value, or part of it).
- `readBytes_succ`: a read in terms of its bytes. A read of known bytes:
  `simp only [readBytes_succ, BitVec.of_length_zero]; decide`.

## What a theorem means

`Block` is defined from the model: `step image state flags` runs one instruction, and
`execute image n state choices` runs `n` of them with one value of the undefined flags per step
(`FlagChoices`). Proofs never mention them; they are what a theorem's meaning rests on.

What a proof does not cover: the decoder (instructions come from the importer and iced-x86), the
CPU (the model is tested against hardware, not proved equal to it), flags other than ZF, CF and
SF, instructions outside the supported subset, and concurrency.

## Importer and checker

- `cargo run -p rivet-import -- ./prog --function f --namespace F --output F.lean` writes
  `F.entry`, `F.program`, `F.regions` (the binary's segments) and `F.Loaded memory` (memory holds
  the segments' bytes).
- `cargo run -p rivet-check -- --cases 1000` tests the model against the CPU.
