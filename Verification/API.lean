module
public import Verification.Syntax
import Verification.Model

public section
namespace Verification.API
noncomputable def Execution := State

/-- Logical observations, not a constructor for an execution. -/
inductive Control where
  | running (pc : Nat)
  | returned (address : Nat)
  | fault
  deriving DecidableEq, Repr

structure View where
  regs : Reg → Nat
  zero : Bool
  bytes : Nat → Fin 256
  readable : Nat → Bool
  reads : List Access
  control : Control

noncomputable def observe (s : Execution) : View :=
  ⟨s.regs, s.zf, s.mem, s.readable, s.reads,
    match s.status with
    | .running => .running s.pc
    | .returned a => .returned a
    | .fault => .fault⟩

@[expose] noncomputable def reg (s : Execution) (r : Reg) : Nat := (observe s).regs r
@[expose] noncomputable def byte (s : Execution) : Nat → Fin 256 := (observe s).bytes
@[expose] noncomputable def readable (s : Execution) : Nat → Bool := (observe s).readable
@[expose] noncomputable def zero (s : Execution) : Bool := (observe s).zero
@[expose] noncomputable def reads (s : Execution) : List Access := (observe s).reads
@[expose] def At (s : Execution) (pc : Nat) : Prop := (observe s).control = .running pc
@[expose] def Returned (s : Execution) (a : Nat) : Prop := (observe s).control = .returned a
noncomputable def execute (p : Program) (n : Nat) (s : Execution) : Execution := run p n s

@[expose] def View.returnAddress (v : View) : Nat :=
  (List.range 8).foldr (fun i n => (v.bytes (v.regs .rsp+i)).val + 256*n) 0
@[expose] def View.ValidReturnSlot (v : View) : Prop :=
  v.regs .rsp + 8 ≤ word ∧ (List.range 8).all (fun i => v.readable (v.regs .rsp+i)) = true
@[expose] noncomputable def returnAddress (s : Execution) : Nat := (observe s).returnAddress
@[expose] def ValidReturnSlot (s : Execution) : Prop := (observe s).ValidReturnSlot

@[expose] abbrev InstructionAt (p : Program) (pc : Nat) (op : Op) : Prop :=
  (p[pc]?).map Instruction.op = some op

/-- An exact-fuel Hoare contract over public observations. -/
structure Ensures (p : Program) (n : Nat) (P Q : View → Prop) : Prop where
  run : ∀ s, P (observe s) → Q (observe (execute p n s))

/-- Compose blocks through their shared intermediate assertion. -/
theorem Ensures.seq (first : Ensures p n P Q) (second : Ensures p m Q R) :
    Ensures p (n+m) P R := by
  constructor
  intro s h
  simpa only [execute, run_add] using second.run (execute p n s) (first.run s h)

/-- Change assertions by implication; no interpreter access is required. -/
theorem Ensures.consequence (h : Ensures p n P Q)
    (pre : ∀ v, P' v → P v) (post : ∀ v, Q v → Q' v) : Ensures p n P' Q' :=
  ⟨fun s hs => post _ (h.run s (pre _ hs))⟩

@[simp] theorem execute_zero (p : Program) (s : Execution) : execute p 0 s = s := by rfl

theorem execute_execute (p : Program) (m n : Nat) (s : Execution) :
    execute p m (execute p n s) = execute p (n+m) s := (run_add p n m s).symm

@[simp] theorem execute_returned (p : Program) (n : Nat) (s : Execution)
    (h : Returned s address) : execute p n s = s := by
  have status : s.status = .returned address := by
    cases hs : s.status <;> simp [Returned, observe, hs] at h ⊢
    assumption
  have step_eq : step p s = s := by simp [step, status]
  change run p n s = s
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, step_eq] using ih

/-- Logical register update; other observations are retained by record update. -/
@[expose] def View.write (v : View) (r : Reg) (n : Nat) : View :=
  { v with regs := fun q => if q = r then n else v.regs q }

private theorem running (hv : observe s = v) (location : v.control = .running pc) :
    s.status = .running ∧ s.pc = pc := by
  have hc : (observe s).control = .running pc := hv ▸ location
  cases hs : s.status <;> simp [observe, hs] at hc ⊢
  exact hc

private theorem one (code : InstructionAt p pc op)
    (hv : observe s = v) (location : v.control = .running pc) :
    execute p 1 s = stepOp op s := by
  have hr := running hv location
  change step p s = stepOp op s
  simp only [step, hr.1, hr.2]
  cases he : p[pc]? with
  | none => simp [InstructionAt, he] at code
  | some i => simp [InstructionAt, he] at code; simp [code]

-- Every instruction has the same contract shape as a multi-instruction block.
-- `code` is checked automatically for concrete programs, or supplied explicitly.
theorem clear (p : Program) (pc : Nat) (dst : Reg32) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.xor dst dst) := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v.write dst.parent 0 with control := .running (pc+1), zero := true }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, View.write, stepOp, next, put]

theorem test_zero (p : Program) (pc : Nat) (r : Reg) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.test r r) := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v with control := .running (pc+1), zero := v.regs r == 0 }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, stepOp, next]

theorem read_byte (p : Program) (pc : Nat) (dst : Reg32) (base : Reg) (v : View)
    (location : v.control = .running pc) (bound : v.regs base < word)
    (allowed : v.readable (v.regs base) = true)
    (code : InstructionAt p pc (.movzx dst (.bytePtr base)) := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v.write dst.parent (v.bytes (v.regs base)).val with
      control := .running (pc+1), reads := v.reads ++ [⟨v.regs base,1⟩] }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  have hb (b : Fin 256) : b.val % word = b.val := by
    apply Nat.mod_eq_of_lt
    have := b.isLt
    unfold word
    omega
  simp_all [observe, View.write, stepOp, next, put]

theorem add (p : Program) (pc : Nat) (dst src : Reg) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.add dst src) := by decide +kernel) :
    let n := (v.regs dst + v.regs src) % word
    Ensures p 1 (· = v) (· = { v.write dst n with control := .running (pc+1), zero := n == 0 }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, View.write, stepOp, next, put]

theorem inc (p : Program) (pc : Nat) (r : Reg) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.inc r) := by decide +kernel) :
    let n := (v.regs r + 1) % word
    Ensures p 1 (· = v) (· = { v.write r n with control := .running (pc+1), zero := n == 0 }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, View.write, stepOp, next, put]

theorem dec (p : Program) (pc : Nat) (r : Reg) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.dec r) := by decide +kernel) :
    let n := (word - 1 + v.regs r) % word
    Ensures p 1 (· = v) (· = { v.write r n with control := .running (pc+1), zero := n == 0 }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, View.write, stepOp, next, put]

theorem branch_zero (p : Program) (pc target : Nat) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.jz target) := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v with control := .running (if v.zero then target else pc+1) }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, stepOp]

theorem branch_nonzero (p : Program) (pc target : Nat) (v : View)
    (location : v.control = .running pc := by rfl)
    (code : InstructionAt p pc (.jnz target) := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v with control := .running (if v.zero then pc+1 else target) }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, stepOp]

theorem return_ (p : Program) (pc : Nat) (v : View)
    (location : v.control = .running pc) (slot : v.ValidReturnSlot)
    (code : InstructionAt p pc .ret := by decide +kernel) :
    Ensures p 1 (· = v) (· = { v.write .rsp ((v.regs .rsp+8)%word) with
      control := .returned v.returnAddress, reads := v.reads ++ [⟨v.regs .rsp,8⟩] }) := by
  constructor
  intro s hv
  have hr := running hv location
  rw [one code hv location]
  cases s
  cases v
  simp_all [observe, View.write, View.ValidReturnSlot, View.returnAddress, stepOp, put, read64]
end Verification.API
