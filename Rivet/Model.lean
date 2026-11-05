module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

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
    -- Keep the symbolic operand last to avoid expanding a word-sized numeral during reduction.
    let v := (word - 1 + s.regs d) % word
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

theorem run_add (p : Program) (n m : Nat) (s : State) :
    run p (n+m) s = run p m (run p n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add, run] using ih (step p s)

end Rivet
