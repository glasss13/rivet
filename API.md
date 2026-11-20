# Rivet API

Everything a proof can use. Names are in `Rivet`, instruction contracts in `Rivet.Contract`.
`Rivet.Internal` is what the tactics build proofs with; a proof never names it. Start each proof
file with

```lean
module
public import Rivet
@[expose] public section
open Rivet
```

Without `module`, Lean computes through the model's internals, which is slow and can exhaust its
recursion limit. Without `public`, files that import this one do not see its names.

## Blocks

- `Block image s c Q`: from `s`, for every value of the undefined flags, execution reaches in
  finitely many steps a state `t` with `Q t` that is `s` except for the change `c`. Functions,
  loops, stretches of code and instructions are all blocks.
- `Changes`: `registers`, a list of registers, and `memory`, a list of regions
  (`memory := [output a, scratch a]`), both empty by default. On two lines, the second field must
  start in the first's column, or Lean reports `expected '}'`.
- `t.Except s c`: every register outside `c.registers` and every read outside `c.memory` is the
  same in `t` as in `s`. Flags, vector registers and the status are not compared; state them in
  `Q`. A register the block saves and restores is not in the change.

While you step from `s`, the goal is `Block image s c Q t`, at the state `t` reached so far. Each
instruction and each block you call runs as a nested block. Only the end is compared with the
start, so a nested block may change what the block keeps if later code restores it.

- `rivet_call copy a (room := proof) as q` runs a block you proved from the current state; give its
  arguments up to its start state. Its preconditions are proved as `rivet_known` does; one that is
  not is an error naming it, and you give it by name. A proof you give is checked as written, over
  the current state: `by rivet_arith [bound]` reads it back, a hypothesis about `s` does not. The
  proof goes on from the block's end with `q_post`, its postcondition read back to the start, and
  `q_kept`, what it left alone (hidden without `as q`). An `∨` postcondition gives one goal per
  side, in order.
- `exact Block.done` ends the block: it proves `Q` and that every store went into a region `c`
  lists, as `rivet_known` does. `Block.done ⟨by rivet_known, by rivet_arith [bound]⟩` takes your
  proof of `Q`.
- `Block.then inner rest` runs a block given as a term, such as a loop:
  `refine Block.then (c₁ := c) (P := P) (Block.loop …) fun u kept post => ?_`, going on from `u`
  with `kept : u.Except t c` and `post : P u`.
- `Block.loop`: a loop whose head is `t`, as a block of its own.

```lean
theorem Block.loop (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
    (body : ∀ current, current.Except t c → invariant current →
      Block image t c (fun next => invariant next ∧ measure next < measure current ∨ exit next) current) :
    Block image t c exit
```

A pass starts at `current`; registers the change does not list read back to `t` through `kept`.
Where it jumps back, prove the invariant with a smaller measure, `Block.done (Or.inl ⟨⟨…⟩, …⟩)`;
where it leaves, `exact Block.done` proves `exit` when `rivet_known` can.

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
  have byte : dst.Has (c.registers .rdi) 1 :=   -- the place of this pass's store
    inv.left.part (Nat.le_refl _) (by rivet_arith [inv])
  rivet_step
  rivet_step
  rivet_step
  rivet_step if more
  · exact Block.done (Or.inl ⟨⟨by rivet_known,
      ⟨by rivet_arith [inv, fits, more], by rivet_arith [inv, fits, more]⟩,
      by rivet_arith [inv, more]⟩, by rivet_arith [inv]⟩)
  · exact Block.done
```

## Reading back

Rivet knows a value by its location: a register (`t.registers .rsp`), its low bits as an
instruction reads them (`(t.registers .rcx).setWidth 32`), the status, a flag, or a read
(`readBytes m p n`). It walks back past every block that could not have touched it, each step a
lookup that computes only with literals; arithmetic over variables is yours (`rivet_arith`):

- a register, from the current state's register equation; at a nested block's end, an unlisted
  register through its change;
- a read, past each store and nested block its region is apart from (see Memory);
- `r.Same m t.memory`, from `t` back to `m`: every store is placed in a region apart from `r`, and
  every nested block's change lists only such regions. A hypothesis `r.Same m m'` ends the walk at
  `m'`.

The walk stops at the block's start (in a loop, `current`) and, for what it changed, at a nested
block's end. There a **fact** says what the location holds: a hypothesis, or a field of a record
hypothesis, `location = value`. So preconditions, invariants and postconditions say where the
registers and frame slots stand, and everything else is stated over the theorem's arguments:

```lean
structure Prepare (a : Arguments) (s : MachineState) : Prop where
  status : s.status = .running 0x4012cb
  output : readBytes s.memory (s.registers .rsp + 8#64) 8 = a.outputAddress
  rsp : s.registers .rsp = a.stackPointer - 16616#64
  capacity : (s.registers .rcx).setWidth 32 = a.outputCapacity
```

With `entry : Prepare a s` in scope, a store through `rsp + 96` is at `a.stackPointer - 16520#64`,
after `mov r10, [rsp+8]` the register `r10` is `a.outputAddress`, and `rivet_arith` needs no
`[entry.rsp]`.

- The first fact in scope for a location is used, a record's fields in order. Registers are read
  before reads, so the slot at `rsp + 8` may come before `rsp`; a read through a pointer kept in a
  slot comes after that slot.
- A fact is used as written: `value = location` is not one. A goal may be either way round.
- A register's fact answers its low bits: with `rcx = v`, `ecx` is `v.setWidth 32`. A fact about
  `ecx` is used when `rcx` has none and says nothing of `rcx`. A fact about 8 bytes says nothing of
  4 of them.
- An equation whose value reads its own location (`rdi = rbx` after `rbx = rdi`), or about a
  location the walk goes past (a register a step wrote), is not a fact, only a hypothesis.
- `abbrev`s, `let`s and record fields are read through; `def`s are not. A record is a `structure`
  in `Prop`, read by the fields you can name, not private ones.

Steps read back their pointers, closing tactics their goals, and `rivet_arith` its listed facts.
Your hypotheses are never changed. Only the program and addresses with no variables in them, such
as the importer's `F.entry`, are evaluated.

`rivet_known` closes a goal without arithmetic or search. It takes the goal apart (`∧`, `∀`,
records; either side of `∨`), and a part closes when, read back, it is a hypothesis or part of one
(a `∀` one when its premises are hypotheses), or its two sides are the same (`x ≤ x` too). Places,
permissions and `r.Apart r'` close by the lookups under Memory. For `∃`, give the witness.

A fact over many addresses (a `∀`) is carried by a lemma you prove once from `r.Same`, such as
`Table16.carry (same : (table a).Same m m') : Table16 m T b → Table16 m' T b`, used as
`table16.carry (by rivet_known)`.

An error shows each part that did not close, as asked and as read back; where each read stopped
and what to prove there; and why each equation left about it is not a fact.

## Stepping

`rivet_step` executes the instruction at the current address through its contract: `rivet_step`,
`rivet_step as t`, `rivet_step if h`, `rivet_step as t if h`. `rivet_step to 0x401380` (`as t`)
steps until the block is at that address, stopping where a single step would.

- **Facts.** The new state gets one equation per field (`status`, `registers`, `memory`, the four
  flags, `xmmRegisters`), over the block's start, named memories and nested-block ends. The values
  written and the branch condition are read back. The previous state and its equations are dropped
  when nothing depends on them. A fact you add mid-block applies to later steps and closing tactics.
- **Names.** `as t` names the state and its facts `t_status`, `t_registers`, `t_memory`, …;
  unnamed, they are hidden. Name a state to state a fact about it.
- **Memory.** Each store makes a memory `mₙ`, named either way, with
  `mₙ_def : mₙ = m.storeBytes p n (littleEndianAt v p)`: `m` the memory before, `p` the pointer,
  `n` the size as a literal, `v` the value.
- **Branches.** A conditional jump is stepped with `if h`, and only it. It gives goals `taken` and
  `fallthrough`, with `h` (negated in `fallthrough`) a statement about words, such as
  `¬x - 1#64 = 0#64`. An arm that cannot run is still a goal; when the condition has a value, `h`
  is `False` there: `exact h.elim`. `iterate`, `repeat` and `rivet_step to` never cross a branch.
- **Return.** After `ret` the status is `.running (readBytes m rsp 8)`, the 8 bytes at `rsp` before
  it.
- **Side conditions.** An access needs a place in a region the image grants (see Memory). Operand
  checks are stated over the block's start; `rivet_step` tries `rfl`, `decide` and `assumption`
  and leaves the rest as goals.

## Arithmetic

A step's facts are about words (`rdi + rax`, `rsp - 8#64`); bounds and invariants are numbers over
`x.toNat`. `rivet_arith [f₁, f₂]` proves goals that mix the two with Lean's `lia`, from the listed
facts alone, after reading the goal and facts back as `rivet_known` does. When `lia` fails, the
error names the facts in scope about the goal's terms that were not listed.

- A listed record (`inv`) is given field by field, and a record goal (`r.Has p n`) is proved field
  by field. A `∀` fact is an error: give it its arguments (`lemma x`).
- It reads `+`, `-`, multiplication by a literal, comparisons, `toNat`, literals, `if`, `>>>`,
  `<<<`, `setWidth`, a mask with a literal (`x &&& 15#64`), and `BitVec.ofNat w n` when `n < 2^w`.
  The contracts state `not` as `-x - 1` and `movsxd` as a sum with an `if`.
- Its budget is a fixed 20000 heartbeats, apart from the declaration's and unchanged by
  `maxHeartbeats`, and covers checking its proof. Facts the goal does not need (`%`, `/`, large
  `∨`s) can keep `lia` from a proof: list only those it needs. A product of two registers can make
  the check too costly: `generalize x * y = p at *` first.
- A term it does not read, such as a signed value, needs a law tagged `@[rivet]` that states it in
  terms it reads. Rivet applies the law wherever it writes a value; state your own facts in its
  form too. Prove laws through `toNat`, not with `bv_decide`, whose proofs trust compiled code. Lean
  has the signed laws:

  ```lean
  attribute [rivet] BitVec.toInt_eq_toNat_cond BitVec.msb_eq_decide BitVec.toNat_signExtend
  ```

- Do not use `bv_omega` in a block's proof: it rewrites every fact about words in scope, can run for
  minutes, and ignores `maxHeartbeats`. In a small lemma of its own it is fine.

## Machine and programs

- `MachineState`: `registers`, `xmmRegisters`, `signFlag`, `zeroFlag`, `carryFlag`,
  `overflowFlag`, `memory`, `status`. `ExecutionStatus`: `running address` or `fault`.
  `MachineState.returnAddress`: the 8 bytes at `rsp`.
- `Reg`, `Reg32`, `Reg16`, `Reg8`, `Xmm`, `Width`, `Address`, `Operand`, `Op`, `Instruction`, `Program`.
- The contract for `Op.x` is `Contract.x`, and for `Op.binary .y`, `Contract.y` (`Contract.mov`,
  `Contract.cmp`): a `Block` whose change is what the instruction writes. Read one to see exactly
  what an instruction does.
- `Block` is defined by `step image state flags`, which runs one instruction, and
  `execute image n state choices`, which runs `n` with one value of the undefined flags per step
  (`FlagChoices`). Proofs never use them; a theorem's meaning rests on them.

## Memory

Memory is named regions, as the state is named registers. Rivet asks one thing of two ranges: is
one inside the other, or are they apart?

- An access needs `image.Reads r` or `image.Writes r` for a region it lies in.
- A read passes a store apart from it, and a nested block when a region it lies in is apart from
  every region the block's change lists.
- A store, and each region a nested block's change lists, must lie in one region of the outer
  change. Two listed regions side by side do not cover a range across both.
- Where several places have an access, the first in scope that answers is used. Rivet never
  searches further.

**Where bytes are.**

- **A place** is a hypothesis `r.Has q n`. A root is placed where it starts, so you state places
  only for regions that are variables. A place that fills its region puts an access a literal
  distance past its pointer in exactly those bytes: with `stack a` rooted at
  `a.stackPointer - 112#64`, the 8 bytes at `a.stackPointer - 48#64` are `(stack a).part 64 8`. A
  place whose size is not a literal places only itself: state the bytes you access,
  `have byte : dst.Has p 1 := left.part (Nat.le_refl _) (by …)`.
- **Two ranges of one root** are compared by their numbers, however the parts were cut:
  `(stack a).part 16 8` lies in `(stack a).part 0 64` and is apart from `((stack a).part 0 112).part 64 8`.
  Other regions are apart by a hypothesis `r.Apart r'`, and granted by `image.Reads r` or
  `image.Writes r`, about regions they lie in: state these for the whole buffers and the stack.
- **Two pointers** that are one expression plus or minus literals (`rsp + 56#64` and `rsp - 8#64`,
  or two literals) are compared by that distance, whatever their regions: a read misses the store
  or is those bytes of the value stored. A store that holds only some of a read's bytes stops the
  walk.
- **Where a read stops,** the error states what to prove: that the read is outside the store
  (`Memory.readBytes_storeBytes_outside`), or where it is inside it (`placed.readBytes_stored`). A
  place you need and do not have is `placed.part start finish`, from its two bounds.

`Memory` is a byte per 64-bit address. `Memory.storeBytes memory base length bytes` writes the
addresses whose value lies in `[base.toNat, base.toNat + length)`. `readBytes memory address size`
is the only read; it and `littleEndianAt` are closed: use the laws.

- `Region` (`base`, `length`, `readable`, `writable`) and `Image` (`program`, `regions`). Name each
  region with an `abbrev`. `Region.root start length readable writable` makes one from a pointer
  (`abbrev stack (a) : Region := Region.root (a.stackPointer - 112#64) 120 true true (by …)`), and
  `r.part offset length` one inside `r` (`abbrev saved (a) : Region := (stack a).part 16 128`).
  Their numbers are only their laws (`Region.root_base`, `Region.part_base`, `Region.root_length`,
  `Region.part_length`, `Region.root_readable`, `Region.root_writable`): `rfl`, `decide`, `dsimp`,
  `change` and `omega` do not see them until you rewrite with the laws. A place that fills a region
  may state its size as the length the region was made with or as `r.length`.
- `r.Has pointer size`, `r.Apart r'`, `r.Same m m'` (the memories agree on every byte of `r`),
  `image.Reads r`, `image.Writes r`. A block that takes regions as arguments states them:
  `(writes : image.Writes dst) (apart : dst.Apart slot)`.

The laws. Bounds are numbers, so `rivet_arith` needs them as facts: a place's (`placed.start`,
`placed.finish`), its region's `r.fits`, and a part's base by `Region.part_base`. A root's base
and every length it reads by their laws.

```lean
Region.fits r : r.base + r.length ≤ 2^64
-- placed : r.Has pointer size
placed.start : r.base ≤ pointer.toNat
placed.finish : pointer.toNat + size ≤ r.base + r.length
-- any bytes inside a place, by their bounds
placed.part (start : pointer.toNat ≤ inner.toNat) (finish : inner.toNat + less ≤ pointer.toNat + size) :
  r.Has inner less
-- a place that fills a region places each part (the lookups do this at literal offsets)
placed.part_at (fills : r.length ≤ size) offset length (inside : offset + length ≤ r.length) (positive : 0 < length) :
  (r.part offset length inside).Has (pointer + BitVec.ofNat 64 offset) length
Region.root_has start length readable writable fits : (Region.root start length readable writable fits).Has start length
Region.root_base start length readable writable fits : (Region.root start …).base = start.toNat
Region.part_base r offset length inside : (r.part offset length inside).base = r.base + offset
-- where a read stops at a store into its own region
Memory.readBytes_storeBytes_outside memory bytes (outside : address.toNat + size ≤ base.toNat ∨ base.toNat + length ≤ address.toNat)
  (fits : address.toNat + size ≤ 2^64) :
  readBytes (memory.storeBytes base length bytes) address size = readBytes memory address size
-- placed : r.Has stored length
placed.readBytes_stored offset (start : pointer.toNat = stored.toNat + offset) (inside : offset + size ≤ length) memory value :
  readBytes (memory.storeBytes stored length (littleEndianAt value stored)) pointer size = value.extractLsb' (8 * offset) (8 * size)
-- same : r.Same earlier later
same.read (placed : r.Has pointer size) : readBytes earlier pointer size = readBytes later pointer size
-- a permission from the image's list; `readable` is `Region.root_readable ..`. `Image.writes_of_mem` likewise
Image.reads_of_mem (member : r ∈ image.regions) (readable : r.readable = true) : image.Reads r
-- two parts that do not meet (the lookups do this at literal offsets)
Region.part_apart r inside inside' (apart : offset + length ≤ offset' ∨ offset' + length' ≤ offset) :
  (r.part offset length inside).Apart (r.part offset' length' inside')
readBytes_one memory address : readBytes memory address 1 = BitVec.ofNat 8 (memory address).val
readBytes_succ memory address size :
  readBytes memory address (size + 1) = readBytes memory (address + 1#64) size ++ BitVec.ofNat 8 (memory address).val
```

To apply a store law at a named step ending with memory `m₁`: `rw [t_memory, m₁_def]`. A read of
known bytes: `simp only [readBytes_succ, BitVec.of_length_zero]; decide`.

## Importer

`cargo run -p rivet-import -- ./prog --function f --namespace F --output F.lean` writes `F.entry`,
`F.program`, `F.region_<a>` for the segment at `a`, `F.regions` (all of them), and
`F.Loaded memory`, whose field `segment_<a> : F.region_<a>.Same F.segment_<a> memory` says memory
is the segment's bytes. A constant read from a segment needs its place and its value as facts:
`have place : F.region_<a>.Has 0x403000#64 8 := by rivet_known`, then
`have value : readBytes s.memory 0x403000#64 8 = 42#64 := by rw [← loaded.segment_<a>.read place]; …`
with the known-bytes recipe above.
