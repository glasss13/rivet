import Std
namespace Verification

def word : Nat := 2^64
inductive Reg where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr
-- Widths are expressed by x86 register aliases and the memory operand type.
inductive Reg32 where
  | eax | edx
  deriving DecidableEq, Repr
@[simp] def Reg32.parent : Reg32 → Reg
  | .eax => .rax
  | .edx => .rdx
structure Mem8 where
  bytePtr ::
  base : Reg
  deriving DecidableEq, Repr
inductive Op where
  | xor (dst src : Reg32)
  | test (lhs rhs : Reg)
  | movzx (dst : Reg32) (src : Mem8)
  | add (dst src : Reg)
  | inc (dst : Reg)
  | dec (dst : Reg)
  | jz (target : Nat)
  | jnz (target : Nat)
  | ret
  deriving DecidableEq, Repr
structure Instruction where
  op : Op
  line : Nat
  deriving DecidableEq, Repr
abbrev Program := List Instruction
structure Access where
  address : Nat
  size : Nat
  deriving DecidableEq, Repr
inductive Status where
  | running | returned (address : Nat) | fault
  deriving DecidableEq, Repr
structure State where
  regs : Reg → Nat
  zf : Bool
  mem : Nat → Fin 256
  readable : Nat → Bool
  pc : Nat
  status : Status
  reads : List Access

def put (s : State) (r : Reg) (v : Nat) : State :=
  { s with regs := fun q => if q = r then v % word else s.regs q }
def next (s : State) : State := { s with pc := s.pc + 1 }
def read64 (m : Nat → Fin 256) (a : Nat) : Nat :=
  (List.range 8).foldr (fun i v => (m (a+i)).val + 256*v) 0

def stepOp (op : Op) (s : State) : State :=
  match op with
  | .xor d r =>
    let v := Nat.xor (s.regs d.parent % 2^32) (s.regs r.parent % 2^32)
    next { put s d.parent v with zf := v == 0 }
  | .test l r => next { s with zf := (s.regs l &&& s.regs r) == 0 }
  | .movzx d b =>
    let a := s.regs b.base
    if a < word && s.readable a then
      next { put s d.parent (s.mem a).val with reads := s.reads ++ [⟨a,1⟩] }
    else { s with status := .fault }
  | .add d r =>
    let v := (s.regs d + s.regs r) % word
    next { put s d v with zf := v == 0 }
  | .inc d =>
    let v := (s.regs d + 1) % word
    next { put s d v with zf := v == 0 }
  | .dec d =>
    let v := (s.regs d + word - 1) % word
    next { put s d v with zf := v == 0 }
  | .jz t => { s with pc := if s.zf then t else s.pc+1 }
  | .jnz t => { s with pc := if s.zf then s.pc+1 else t }
  | .ret =>
    let a := s.regs .rsp
    if a + 8 ≤ word && (List.range 8).all (fun i => s.readable (a+i)) then
      { put s .rsp (a+8) with status := Status.returned (read64 s.mem a), reads := s.reads ++ [⟨a,8⟩] }
    else { s with status := .fault }

def step (p : Program) (s : State) : State :=
  match s.status with
  | .running => match p[s.pc]? with
    | some i => stepOp i.op s
    | none => { s with status := .fault }
  | _ => s

def run (p : Program) : Nat → State → State
  | 0, s => s
  | n+1, s => run p n (step p s)

-- Only ZF is observable by this language. No instruction writes memory.
theorem step_memory (p : Program) (s : State) : (step p s).mem = s.mem := by
  unfold step
  split
  · split
    · rename_i i h
      cases i.op <;> simp [stepOp, next, put] <;> split <;> rfl
    · rfl
  · rfl

theorem run_memory (p : Program) (n : Nat) (s : State) : (run p n s).mem = s.mem := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, ih, step_memory]
end Verification
