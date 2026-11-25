# Rivet API

Public names live in `Rivet`; instruction specs live in `Rivet.Contract`. Never reference `Rivet.Internal`.

Start every proof file with:

```lean
module
public import Rivet
@[expose] public section
open Rivet
```

`module` stops Lean from unfolding model internals (preventing slowness and recursion-limit hits). `public import` and `@[expose] public section` make theorems visible to importing files.

## Blocks & Loops

- `Block code s c Q` (5th arg `t := s` is the current state while stepping): given `s.Holds code`, for all undefined flag values, execution reaches a state `t` with `Q t` and `t.Except s c`. `block.run holds choices` unpacks that into `∃ final, (∃ steps, execute steps s choices = final) ∧ final.Except s c ∧ Q final`.
- `Changes`: `{ registers := [...], xmm := [...], memory := [...], kernel := true }` (`registers : List Reg`, `xmm : List Xmm`, all default `[]`; `kernel : Bool`, default `false`). Multi-line fields must start in the same column, or Lean reports `expected '}'`.
- `t.Except s c`: every register not in `c.registers`, every `xmmRegisters` entry not in `c.xmm`, and every memory read disjoint from `c.memory` equals `s`; and `t.kernel = s.kernel` unless `c.kernel`. Does not cover flags or `status` (state those in `Q`). Saved-and-restored registers do not need to be listed.

Closing and composing blocks:

- `exact Block.done` — ends the block, proving `Q` and `t.Except s c` via `rivet_known` (tries both sides of `∨` in `Q`).
- `exact Block.done proofOfQ` — supply `Q` explicitly (e.g. `⟨by rivet_known, by rivet_arith [bound]⟩`); `t.Except s c` is still proved automatically.
- `Block.then` — run a block term (such as a loop) and continue from its end state:
  `refine Block.then (c₁ := c) (P := P) (Block.loop …) fun u kept post => ?_`
- `Block.loop` — prove a loop starting at `t`:

```lean
Block.loop (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
  (body : ∀ cur, cur.Except t c → invariant cur →
    Block code t c (fun next => invariant next ∧ measure next < measure cur ∨ exit next) cur) :
  Block code t c exit
```

Example:

```lean
-- mov [rdi], sil · inc rdi · dec rdx · jne 0x1000
structure Filling (dst : Region) (s t : MachineState) : Prop where
  status : t.status = .running 0x1000
  left : dst.Has (t.registers .rdi) (t.registers .rdx).toNat
  positive : 0 < (t.registers .rdx).toNat

theorem fill (dst : Region) (s : MachineState) (writes : s.kernel.Writes dst) (start : Filling dst s s) :
    Block code s { registers := [.rdi, .rdx], memory := [dst] } (fun t => t.status = .running 0x100b) := by
  refine Block.loop (Filling dst s) (fun t => (t.registers .rdx).toNat) start fun cur kept inv => ?_
  have fits := dst.fits
  have byte : dst.Has (cur.registers .rdi) 1 := inv.left.part (Nat.le_refl _) (by rivet_arith [inv])
  rivet_step; rivet_step; rivet_step
  rivet_step if more
  · exact Block.done (Or.inl ⟨⟨by rivet_known,
      ⟨by rivet_arith [inv, fits, more], by rivet_arith [inv, fits, more]⟩,
      by rivet_arith [inv, more]⟩, by rivet_arith [inv]⟩)
  · exact Block.done
```

## Tactics

### `rivet_step`

Executes instructions at the current PC:
- `rivet_step` / `rivet_step as t` / `rivet_step if h` / `rivet_step as t if h`
- `rivet_step to <addr>` / `rivet_step to <addr> as t` — steps until PC is `<addr>` (stops before branches).

Details:
- `as t` names the next state `t` and equations `t_status`, `t_registers`, `t_memory`, `t_kernel`, `t_zeroFlag`, `t_carryFlag`, `t_signFlag`, `t_overflowFlag`, `t_xmmRegisters` (anonymous without `as`). Unused prior states are auto-cleared.
- Every store introduces `mₙ` and `mₙ_def : mₙ = m.storeBytes p n (littleEndianAt v p)`.
- Conditional jumps (`jcc`) require `if h` (and only `jcc` allows `if h`). Produces goals `taken` (with `h`) and `fallthrough` (with `¬h`) as word comparisons. Unreachable branches get `h : False` (`exact h.elim`). `iterate`, `repeat`, and `rivet_step to` never cross a branch.
- `ret` sets `status = .running (readBytes m rsp 8)`.
- `syscall` dispatches on `rax`, which must trace back to a literal (e.g. `mov eax, 231` or `s.registers .rax = 231#64`). `exit_group` (231) sets `status = .exited ((t.registers .rdi).setWidth 8)` and ends execution (`exact Block.done`).
- Memory accesses require an in-bounds `r.Has p n` and a `s.kernel.Reads r` / `s.kernel.Writes r` hypothesis (errors otherwise). State it at the block's start `s`: no instruction changes the kernel, so it holds at every step. Other side conditions try `rfl`/`decide`/`assumption`; any remainder becomes a subgoal.

### `rivet_call`

```lean
rivet_call lemma arg1 arg2 (precond := proof) as q
```

- Pass positional args up to (not including) the start state `s`. `Prop` preconditions are auto-proved via `rivet_known`; pass missing ones by name `(precond := proof)`.
- Named proofs are checked at the **current** state: use `by rivet_arith [...]` (which traces back to `s`), not a raw hypothesis about `s`.
- `as q` introduces end state `q`, `q_kept : q.Except prev c₁`, and `q_post : P q` (anonymous without `as`).
- If `P` is a disjunction (`A ∨ B`), splits into one goal per branch in order.

### `rivet_known`

Closes goals with no arithmetic and no search. Splits `∧`, `∀`, and `Prop` `structure`s; tries both sides of `∨` (provide witnesses for `∃`). After tracing values back to start, closes a subgoal if it:
- matches a hypothesis (or a `∀` hypothesis whose premises are in scope),
- is reflexive (`x = x`, `x ≤ x`) or a closed literal,
- or resolves via region rules (`Has`, `Apart`, `Reads`, `Writes`, `Same`).

### `rivet_arith [h₁, h₂, ...]`

Traces the goal and listed hypotheses back to start, then runs `lia +ac` using **only** the listed hypotheses.

- Splits `Prop` `structure` goals (e.g. `r.Has p n`) and `Prop` `structure` hypotheses (e.g. `inv`) into fields automatically.
- Never pass a `∀` lemma directly — instantiate it (`lemma x`).
- Supported: `+`, `-`, `* literal`, `<`/`≤`/`=`, `toNat`, literals, `if`, `>>>`, `<<<`, `setWidth`, literal bitmasks (`x &&& 15#64`), `BitVec.ofNat w n` (when `n < 2^w`).
- Fixed 20,000-heartbeat budget (unchanged by `maxHeartbeats`). List only needed facts (extra `%`, `/`, or big `∨` can block `lia`). For nonlinear products `x * y`, run `generalize x * y = p at *` first.
- For unsupported ops (e.g. `toInt`, `msb`, `signExtend`), tag rewrite lemmas `@[rivet]` (prove via `toNat`, not `bv_decide`). Built-in signed laws:
  ```lean
  attribute [rivet] BitVec.toInt_eq_toNat_cond BitVec.msb_eq_decide BitVec.toNat_signExtend
  ```
- Avoid `bv_omega` inside `Block` proofs (rewrites the whole context, can hang, ignores `maxHeartbeats`). Fine in small standalone lemmas.

## Automatic Value Tracing

Rivet automatically traces `t.registers r`, `(t.registers r).setWidth k`, `t.xmmRegisters r`, `t.status`, flags, `t.kernel`, `readBytes m p n`, and `r.Same m t.memory` back through steps, disjoint stores, and unmodified nested-block fields to the block's start state (or the last nested block that modified them). A hypothesis `r.Same m m'` stops a `Same` trace at `m'`.

Any hypothesis (or public field of a `Prop` `structure` hypothesis) of the form `loc = expr` at the start state—or at the end of a nested block that modified `loc`—is substituted automatically:

```lean
structure Prepare (a : Args) (s : MachineState) : Prop where
  status : s.status = .running 0x4012cb
  output : readBytes s.memory (s.registers .rsp + 8#64) 8 = a.outputAddress
  rsp : s.registers .rsp = a.stackPointer - 16616#64
  capacity : (s.registers .rcx).setWidth 32 = a.outputCapacity
```

With `entry : Prepare a s` in scope, a store to `rsp + 96` resolves to `a.stackPointer - 16520#64`, `mov r10, [rsp+8]` sets `r10 = a.outputAddress`, and `rivet_arith` does not need `[entry.rsp]`.

Rules:
- Direction matters: `loc = expr` is substituted; `expr = loc` is ignored (goals work either way).
- First matching equality in scope wins (`structure` fields in order). Register equalities apply before memory reads, so `readBytes s.memory (s.registers .rsp + 8#64) 8 = ...` may precede `rsp = ...`, whereas a read through a pointer stored in memory must come after that slot.
- `s.registers .rcx = v` also resolves `(s.registers .rcx).setWidth 32`, not vice versa. An 8-byte read does not resolve a 4-byte read.
- Cyclic equalities (`rdi = rbx` after `rbx = rdi`) and equalities on intermediate stepped states are ignored. Mid-block `have` equalities apply to subsequent steps and tactics.
- Unfolds `abbrev`, `let`, and public `Prop` `structure` fields; never unfolds `def` or private fields.
- Quantified memory invariants (`∀` / `def`): prove a carry lemma from `r.Same m m'` once and apply `h.carry (by rivet_known)`.

## Memory & Regions

`Memory := BitVec 64 → Fin 256`. `m.storeBytes p n bytes` overwrites `[p.toNat, p.toNat + n)`. `readBytes m p n : BitVec (8 * n)` is little-endian. Both `readBytes` and `littleEndianAt` are opaque — use the lemmas below.

### Regions

Name every region with `abbrev` (not `def`):
- `Region.root start len readable writable fits` — root region (`start.toNat + len ≤ 2^64`).
- `r.part offset len inside` — sub-region at `[r.base + offset, r.base + offset + len)`.
- Predicates: `r.Has p n` (`n` bytes at `p` are in `r`), `r.Apart r'` (disjoint), `r.Same m₁ m₂` (byte-equal on `r`), `k.Reads r`, `k.Writes r` (the kernel `k`, usually `s.kernel`, lets the process read or write all of `r`).

`Region.root` and `Region.part` are opaque: `rfl`/`dsimp`/`decide`/`omega` do not unfold `.base`, `.length`, `.readable`, or `.writable` — rewrite with the accessor lemmas below. (`rivet_arith` auto-applies `Region.root_base` and length laws, but not `Region.part_base`.)

### What Rivet resolves automatically (literal offsets/sizes only)

- **Sub-regions of one root**: containment and `Apart` are checked numerically regardless of `.part` nesting.
- **Distinct roots**: state `r.Apart r'` and `s.kernel.Reads r` / `s.kernel.Writes r` on whole buffers/stack; sub-regions inherit them.
- **Bounds (`r.Has p n`)**:
  - `Region.root` automatically satisfies `r.Has start len`.
  - A literal-sized `r.Has base len` automatically covers literal-offset accesses inside `[base, base + len)` (narrowing to the exact `r.part` when `len` matches `r`'s length). With `r.Has base r.length` (or `r`'s length), `rivet_known` also proves `(r.part off k).Has (base + off) k` for any `off` and literal `k`.
  - Variable lengths (e.g. `capacity`) or computed pointers (`base + i`) need an explicit `have : r.Has p n := h.part ...` before stepping.
  - **First matching `r.Has` in scope wins**: if a broad region precedes a narrower sub-region, reads may bind to the broad region and fail disjointness against writes to another part of it.
- **Same-base pointers with literal offsets** (`rsp + 56#64` vs `rsp - 8#64`, or two literals): Rivet skips disjoint stores and extracts bytes from enclosing stores directly. Partial overlaps stop tracing.
- **Block frame coverage**: every store and every region in a nested `c₁.memory` must lie within a single region listed in the outer `c.memory` (adjacent regions do not combine).

### Lemmas

```lean
Region.fits r : r.base + r.length ≤ 2^64

-- h : r.Has p n
h.start  : r.base ≤ p.toNat
h.finish : p.toNat + n ≤ r.base + r.length
h.part (start : p.toNat ≤ q.toNat) (finish : q.toNat + k ≤ p.toNat + n) : r.Has q k
h.part_at (fills : r.length ≤ n) offset len (inside : offset + len ≤ r.length) (pos : 0 < len) :
  (r.part offset len inside).Has (p + BitVec.ofNat 64 offset) len

Region.root_has start len r w fits : (Region.root start len r w fits).Has start len
-- Accessors (Region.root and Region.part are opaque):
-- Region.root_base (= start.toNat), Region.root_length (= len), Region.root_readable, Region.root_writable
-- Region.part_base (= r.base + off), Region.part_length (= len)
Region.part_apart r inside inside' (apart : off + len ≤ off' ∨ off' + len' ≤ off) :
  (r.part off len inside).Apart (r.part off' len' inside')

Kernel.Writes.reads (w : k.Writes r) : k.Reads r

-- same : r.Same m₁ m₂
same.read (h : r.Has p n) : readBytes m₁ p n = readBytes m₂ p n

Memory.readBytes_storeBytes_outside m bytes
  (outside : addr.toNat + sz ≤ base.toNat ∨ base.toNat + len ≤ addr.toNat)
  (fits : addr.toNat + sz ≤ 2^64) :
  readBytes (m.storeBytes base len bytes) addr sz = readBytes m addr sz

-- h : r.Has stored len
h.readBytes_stored offset (start : p.toNat = stored.toNat + offset) (inside : offset + sz ≤ len) m val :
  readBytes (m.storeBytes stored len (littleEndianAt val stored)) p sz = val.extractLsb' (8 * offset) (8 * sz)

readBytes_one  m p   : readBytes m p 1 = BitVec.ofNat 8 (m p).val
readBytes_succ m p n : readBytes m p (n + 1) = readBytes m (p + 1#64) n ++ BitVec.ofNat 8 (m p).val
```

Recipes:
- Rewrite at a named store step: `rw [t_memory, m₁_def]`
- Evaluate a read of constant bytes: `simp only [readBytes_succ, BitVec.of_length_zero]; decide`

## Machine, Contracts & Importer

- `MachineState`: `registers`, `xmmRegisters`, `signFlag`, `zeroFlag`, `carryFlag`, `overflowFlag`, `memory`, `kernel`, `status` (`ExecutionStatus.running addr | .exited code | .fault`; `code : BitVec 8` is the process's exit code). `s.returnAddress := readBytes s.memory (s.registers .rsp) 8`.
- `Access`: `.unmapped | .protNone | .readOnly | .readExec | .readWrite`.
- `Kernel`: `{ access : BitVec 64 → Access }`, with projections `mapped`, `readable`, `writable`, `executable`. An instruction faults on an access `readable` / `writable` does not allow, and none changes the kernel. `Kernel.Writes` implies `Kernel.Reads`.
- Syntax types: `Reg`, `Reg32`, `Reg16`, `Reg8`, `Xmm`, `Width`, `Address`, `Operand`, `Op`.
- `Code := BitVec 64 → Option (Fin 256)`. Handwritten bytes: `Code.ofBytes 0x1000 [0x53, 0xc3]`.
- `s.code` reads executable memory. `s.Holds code` requires each specified byte to match memory at a `.readExec` address.
- Instruction specs: `Rivet.Contract.<op>` (`Contract.mov`, `Contract.add`, `Contract.cmp`, etc.). Note: `not` is `-x - 1`; `movsxd` is a sum with `if`.
- `Op.syscall` has one spec per system call (e.g. `Contract.exitGroup` for Linux `exit_group`, `rax = 231#64`: changes only `status` to `.exited ((s.registers .rdi).setWidth 8)`).
- `step`, `execute`, `FlagChoices` define `Block` (proofs never call them).
- Importer:
  ```sh
  cargo run -p rivet-import -- ./prog --namespace F --output F.lean
  ```
  Generates `F.file`, `F.layout`, `F.layout_ok`, `F.code := F.file.code F.layout`, and per-segment `F.segment_<a>`, `F.region_<a>`, and `F.bytes_<a>`.

## Loader

- `Exe` (`{ size, pages }`): ELF bytes in 4096-byte little-endian base-256 `Nat` pages (`file.u8`/`.u16`/`.u32`/`.u64`).
- `file.layout : Option Layout` (`{ entry : BitVec 64, segments : List Segment }`): checks static non-PIE x86-64 ELF64 (`-z noexecstack`, W^X, ascending non-overlapping pages, `e_entry` in executable bytes). Check once: `theorem layout_ok : file.layout = some layout := by decide +kernel`.
- `Segment`: `segment.region` (mapped 4 KiB pages), `segment.bytes` (`[p_vaddr, p_vaddr + p_memsz)`), `segment.memory file` (file bytes + zero BSS).
- `Starts file layout stack s`: start-state hypothesis (`status`, `access`, `same`, `apart`, `stackWrites`, `stackPages`, `rsp`, `aligned`), plus `starts.reads`, `starts.writes`, and `starts.holds : s.Holds (file.code layout)`.
- Pull `starts.reads`/`starts.writes`/`starts.same` onto the importer's `F.region_<a>` / `F.bytes_<a>` aliases:
  ```lean
  have writes : s.kernel.Writes F.region_403000 := starts.writes F.segment_403000 (by decide) rfl
  have same : F.bytes_403000.Same (F.segment_403000.memory F.file) s.memory :=
    starts.same F.segment_403000 (by decide)
  ```
