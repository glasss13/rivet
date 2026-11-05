module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

inductive ExecutionStatus where
  | running (instructionIndex : Nat)
  | returned (address : Nat)
  | fault
  deriving DecidableEq, Repr
structure MachineState where
  registers : Reg → Nat
  zeroFlag : Bool
  memory : Nat → Fin 256
  readable : Nat → Bool
  status : ExecutionStatus
  readHistory : List Access

def put (s : MachineState) (r : Reg) (v : Nat) : MachineState :=
  { s with registers := fun q => if q = r then v % word else s.registers q }
def ExecutionStatus.isRunning : ExecutionStatus → Bool
  | .running _ => true
  | _ => false

def ExecutionStatus.advance : ExecutionStatus → ExecutionStatus
  | .running index => .running (index + 1)
  | stopped => stopped

def next (s : MachineState) : MachineState := { s with status := s.status.advance }
def read64 (m : Nat → Fin 256) (a : Nat) : Nat :=
  (List.range 8).foldr (fun i v => (m (a+i)).val + 256*v) 0

def stepOp (op : Op) (s : MachineState) : MachineState :=
  match op with
  | .xor d r =>
    let v := Nat.xor (s.registers d.parent % 2^32) (s.registers r.parent % 2^32)
    next { put s d.parent v with zeroFlag := v == 0 }
  | .test l r => next { s with zeroFlag := (s.registers l &&& s.registers r) == 0 }
  | .movzx d b =>
    let a := s.registers b.base
    if a < word && s.readable a then
      next { put s d.parent (s.memory a).val with readHistory := s.readHistory ++ [⟨a,1⟩] }
    else { s with status := .fault }
  | .add d r =>
    let v := (s.registers d + s.registers r) % word
    next { put s d v with zeroFlag := v == 0 }
  | .inc d =>
    let v := (s.registers d + 1) % word
    next { put s d v with zeroFlag := v == 0 }
  | .dec d =>
    -- Keep the symbolic operand last to avoid expanding a word-sized numeral during reduction.
    let v := (word - 1 + s.registers d) % word
    next { put s d v with zeroFlag := v == 0 }
  | .jz t => { s with status := if s.zeroFlag then .running t else s.status.advance }
  | .jnz t => { s with status := if s.zeroFlag then s.status.advance else .running t }
  | .ret =>
    let a := s.registers .rsp
    if a + 8 ≤ word && (List.range 8).all (fun i => s.readable (a+i)) then
      { put s .rsp (a+8) with status := ExecutionStatus.returned (read64 s.memory a), readHistory := s.readHistory ++ [⟨a,8⟩] }
    else { s with status := .fault }

def step (p : Program) (s : MachineState) : MachineState :=
  match s.status with
  | .running index => match p[index]? with
    | some i => stepOp i.op s
    | none => { s with status := .fault }
  | _ => s

def run (p : Program) : Nat → MachineState → MachineState
  | 0, s => s
  | n+1, s => run p n (step p s)

-- Only ZF is observable by this language. No instruction writes memory.
theorem step_memory (p : Program) (s : MachineState) : (step p s).memory = s.memory := by
  unfold step
  split
  · split
    · rename_i i h
      cases i.op <;> simp [stepOp, next, put] <;> split <;> rfl
    · rfl
  · rfl

theorem run_memory (p : Program) (n : Nat) (s : MachineState) : (run p n s).memory = s.memory := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, ih, step_memory]

theorem run_add (p : Program) (n m : Nat) (s : MachineState) :
    run p (n+m) s = run p m (run p n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add, run] using ih (step p s)

end Rivet
