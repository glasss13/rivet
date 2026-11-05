import Verification.Safety
import Verification.Beyond
import Verification.Omit
namespace Verification

def exampleState (n : Nat) : State := {
  regs := fun r => match r with | .rdi => 1024 | .rsi => n | .rsp => 512 | _ => 0
  zf := false
  mem := fun a => if a = 1024 then ⟨42, by decide⟩ else ⟨0, by decide⟩
  readable := fun a => (512 ≤ a && a < 520) || (1024 ≤ a && a < 1024+n)
  pc := 0
  status := .running
  reads := [] }

theorem example_preconditions (n : Nat) (hn : n ≤ 1) :
    Preconditions (exampleState n) 1024 n := by
  refine ⟨rfl, rfl, rfl, rfl, by omega, ?_, ?_, ?_, ?_⟩
  · constructor
    · unfold word; omega
    · intro i hi
      simp [exampleState]
      omega
  · simp [Stack, exampleState, List.range_succ, word]
  · intro r
    cases r <;> simp [exampleState, word] <;> omega
  · intro i j hi hj
    simp [exampleState]
    omega

-- Empty input must not be read. Removing the entry branch attempts exactly that read.
theorem beyond_counterexample :
    (run Beyond.program 2 (exampleState 0)).pc = 2 ∧
    (run Beyond.program 2 (exampleState 0)).regs .rdi = 1024 ∧
    (exampleState 0).readable 1024 = false ∧
    (run Beyond.program 3 (exampleState 0)).status = .fault := by decide +kernel

-- The premature decrement omits the sole byte: native and modeled return zero, expected 42.
theorem omission_counterexample :
    byteSum (exampleState 1).mem 1024 1 = 42 ∧
    (run Omit.program 5 (exampleState 1)).regs .rax = 0 ∧
    (run Omit.program 5 (exampleState 1)).status = .returned 0 := by decide +kernel

#print axioms beyond_counterexample
#print axioms omission_counterexample
end Verification
