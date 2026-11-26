module
public import Rivet.Interpreter.Machine
import Rivet.Laws.Memory
import all Rivet.Interpreter.Machine
import all Rivet.Interpreter.Decode
-- Code-fetch agreement and preservation of executable bytes across execution.
@[expose] public section
namespace Rivet

abbrev InstructionAt (code : Code) (address : BitVec 64) (length : Nat) (operation : Op) : Prop :=
  code.fetch address = some (length, operation)

def MachineState.Holds (state : MachineState) (code : Code) : Prop :=
  ∀ address byte, code address = some byte →
    state.kernel.access address = .readExec ∧ state.memory address = byte

theorem MachineState.Holds.fetch {s : MachineState} {code : Code} (holds : s.Holds code)
    (fetched : code.fetch address = some (length, op)) : s.code.fetch address = some (length, op) := by
  suffices read : ∀ fuel offset front,
      Code.fetch.read code address fuel offset front = some (length, op) →
      Code.fetch.read s.code address fuel offset front = some (length, op) from read _ _ _ fetched
  intro fuel
  induction fuel with
  | zero => simp [Code.fetch.read]
  | succ fuel ih =>
    intro offset front h
    cases hb : code (address + BitVec.ofNat 64 offset) with
    | none => simp [Code.fetch.read, hb] at h
    | some byte =>
      obtain ⟨perm, value⟩ := holds _ _ hb
      have live : s.code (address + BitVec.ofNat 64 offset) = some byte := by
        simp [MachineState.code, Kernel.executable, perm, Access.executable, value]
      simp [Code.fetch.read, hb, live] at h ⊢
      cases reply : feed front byte <;> rw [reply] at h <;> first | exact h | exact ih _ _ h

private theorem keptByte {s : MachineState} (allowed : permits s.kernel.writable base size = true)
    (exec : s.kernel.access address = .readExec) :
    s.memory.storeBytes base size bytes address = s.memory address := by
  unfold Memory.storeBytes
  split
  next h =>
    have := (Internal.permits_iff.mp allowed).2 address h.1 h.2
    simp [Kernel.writable, exec, Access.writable] at this
  next => rfl

private theorem operandKept (s : MachineState) (dest : Operand) (value : BitVec 64)
    (allowed : s.canWrite dest = true) (exec : s.kernel.access address = .readExec)
    (same : s.memory address = byte) :
    (s.writeOperand64 dest value).kernel.access address = .readExec ∧
    (s.writeOperand64 dest value).memory address = byte := by
  cases dest <;> simp [MachineState.writeOperand64, MachineState.write, MachineState.writeMemory, exec, same]
  exact (keptByte (by simpa [MachineState.canWrite] using allowed) exec).trans same

private theorem canWrite_lea {s : MachineState} {d : Operand} (h : validLea d = true) : s.canWrite d = true := by
  cases d <;> simp_all [validLea, MachineState.canWrite]

private theorem canWrite_shift {s : MachineState} {d : Operand} {n : Nat} (h : validShift d n = true) : s.canWrite d = true := by
  cases d <;> simp_all [validShift, MachineState.canWrite]

private theorem canWrite_cmov {s : MachineState} {d src : Operand} (h : validConditionalMove d src = true) : s.canWrite d = true := by
  cases d <;> simp_all [validConditionalMove, MachineState.canWrite]

private theorem stepOp_holds (holds : s.Holds code) :
    (stepOp op pc s flags).Holds code := by
  intro address byte fetched
  obtain ⟨exec, value⟩ := holds address byte fetched
  cases op <;> simp only [stepOp, MachineState.binary, next, MachineState.write, MachineState.writeMemory]
  all_goals repeat' first
    | exact ⟨exec, value⟩
    | exact ⟨exec, (keptByte (by assumption) exec).trans value⟩
    | apply operandKept _ _ _ _ exec value
    | split
  all_goals try simp only [validImul, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
  all_goals grind [canWrite_lea, canWrite_shift, canWrite_cmov]

theorem MachineState.Holds.step {code : Code} (holds : s.Holds code) (flags : FlagValues) : (step s flags).Holds code := by
  unfold Rivet.step
  split <;> try exact holds
  split <;> first | exact stepOp_holds holds | exact holds

theorem MachineState.Holds.execute {code : Code} (holds : s.Holds code) (steps : Nat) (choices : FlagChoices) :
    (execute steps s choices).Holds code := by
  induction steps generalizing s choices with
  | zero => rwa [Rivet.execute]
  | succ n ih => rw [Rivet.execute]; exact ih (holds.step _) _

end Rivet
