import Rivet
-- A plain consumer: it only imports `Rivet`, so it sees every definition's body.
-- Closed definitions must still never be computed through by accident.
open Rivet
set_option linter.unusedVariables false

namespace PlainConsumer
variable (regions : List Region) (r : Reg → BitVec 64)

def prog : Program := [
  ⟨0x1000, 4, .mov (.memory .qword {base := some .rbx, displacement := -8}) (.reg64 .rax)⟩,
  ⟨0x1004, 4, .mov (.reg64 .rcx) (.memory .qword {base := some .rbx, displacement := -8})⟩,
  ⟨0x1008, 5, .movzx .edx (.memory .byte {base := some .rsi, index := some .rcx, scale := .four, displacement := -1})⟩]

/-- A proposition kept out of reach of `assumption` and `simp [*]` until unwrapped. -/
def Later (p : Prop) : Prop := p

-- 1. A store with no permission hypothesis leaves the reduced `case writable`.
example (s : MachineState) (h : s.status = .running 0x1000)
    (later : Later (permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true)) :
    Ensures ⟨prog, regions⟩ (· = s) (fun _ => True) := by
  rivet_step
  case writable =>
    guard_target =ₛ permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true
    exact later
  exact Ensures.refl.consequence (fun _ h => h) (fun _ _ => trivial)

-- 2. Store then load through the same slot.
example (s : MachineState) (h : s.status = .running 0x1000)
    (writable : permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true)
    (readable : permits (Image.readable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true) :
    Ensures ⟨prog, regions⟩ (· = s) (fun f => f.registers .rcx = s.registers .rax) := by
  rivet_step
  rivet_step
  exact Ensures.refl.consequence (fun _ h => h) (fun _ e => by
    subst e
    have fits := permits_valid writable
    simp (disch := bv_omega) [*, Memory.readBytes_storeBytes_within])

-- 3. A frame permission narrowed by a caller's discharger.
example (s : MachineState) (h : s.status = .running 0x1000)
    (frame : permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 112#64)
      (s.registers .rbx + 8#64) = true)
    (low : 112#64 ≤ s.registers .rbx) (high : s.registers .rbx ≤ s.registers .rbx + 8#64) :
    Ensures ⟨prog, regions⟩ (· = s) (fun _ => True) := by
  rivet_step (disch := (apply permits_within frame <;> bv_omega))
  exact Ensures.refl.consequence (fun _ h => h) (fun _ _ => trivial)

-- 4. A scaled index with a negative displacement.
example (s : MachineState) (h : s.status = .running 0x1008)
    (later : Later (permits (Image.readable ⟨prog, regions⟩)
      (s.registers .rsi + s.registers .rcx * 4#64 - 1#64)
      (s.registers .rsi + s.registers .rcx * 4#64 - 1#64 + 1#64) = true)) :
    Ensures ⟨prog, regions⟩ (· = s) (fun _ => True) := by
  rivet_step
  case readable =>
    guard_target =ₛ permits (Image.readable ⟨prog, regions⟩)
      (s.registers .rsi + s.registers .rcx * 4#64 - 1#64)
      (s.registers .rsi + s.registers .rcx * 4#64 - 1#64 + 1#64) = true
    exact later
  exact Ensures.refl.consequence (fun _ h => h) (fun _ _ => trivial)

-- 5. `move` applied by hand: its default finds the reduced permission.
example (s : MachineState) (h : s.status = .running 0x1000)
    (writable : permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true) : True := by
  have := move ⟨prog, regions⟩ 0x1000 (.memory .qword {base := some .rbx, displacement := -8})
    (.reg64 .rax) s (code := by rivet_fetch)
  trivial

-- With no matching hypothesis in reach, the caller proves the reduced permission.
example (s : MachineState) (h : s.status = .running 0x1000)
    (later : Later (permits (Image.writable ⟨prog, regions⟩) (s.registers .rbx - 8#64)
      (s.registers .rbx - 8#64 + 8#64) = true)) : True := by
  have writable : s.canWrite ⟨prog, regions⟩
      (.memory .qword {base := some .rbx, displacement := -8}) = true := by
    simp only [rivet]
    exact later
  have := move ⟨prog, regions⟩ 0x1000 (.memory .qword {base := some .rbx, displacement := -8})
    (.reg64 .rax) s (code := by rivet_fetch) (writable := writable)
  trivial

-- 6. An unrelated goal closes by `assumption` beside a raw permission fact.
example (image : Image) (s : MachineState) (h : s.status = .running 0x1005)
    (fact : s.canWrite image (.memory .qword {base := some .rbx, displacement := -8}) = true) :
    s.status = .running 0x1005 := by
  assumption

example (image : Image) (s : MachineState)
    (fact : s.canWrite image (.memory .qword {base := some .rbx, displacement := -8}) = true)
    (h : s.status = .running 0x1005) :
    s.status = .running 0x1005 := by
  assumption

-- 7. `rfl` on a raw access condition fails without computing; the `rivet` set reduces it.
example (image : Image) (s : MachineState)
    (writable : permits image.writable (s.registers .rbx - 8#64) (s.registers .rbx - 8#64 + 8#64) = true) :
    s.canWrite image (.memory .qword {base := some .rbx, displacement := -8}) = true := by
  fail_if_success rfl
  simpa only [rivet] using writable

-- 8. Normal forms.
example (x : BitVec 64) (h : Address.evaluate {base := some .rbx, displacement := 8} r = x) : True := by
  simp only [rivet] at h
  guard_hyp h :ₛ r .rbx + 8#64 = x
  trivial
example (x : BitVec 64) (h : Address.evaluate {base := some .rbx, displacement := -8} r = x) : True := by
  simp only [rivet] at h
  guard_hyp h :ₛ r .rbx - 8#64 = x
  trivial
example (x : BitVec 64) (h : Address.evaluate {base := some .rdi} r = x) : True := by
  simp only [rivet] at h
  guard_hyp h :ₛ r .rdi = x
  trivial
example (x : BitVec 64)
    (h : Address.evaluate {base := some .rsi, index := some .rcx, scale := .four, displacement := 16} r = x) :
    True := by
  simp only [rivet] at h
  guard_hyp h :ₛ r .rsi + r .rcx * 4#64 + 16#64 = x
  trivial
example (x : BitVec 64)
    (h : Address.evaluate {base := some .rsi, index := some .rcx, scale := .one, displacement := -1} r = x) :
    True := by
  simp only [rivet] at h
  guard_hyp h :ₛ r .rsi + r .rcx - 1#64 = x
  trivial
example (x : BitVec 64) (h : Address.evaluate {displacement := 0x402000} r = x) : True := by
  simp only [rivet] at h
  guard_hyp h :ₛ 0x402000#64 = x
  trivial
example (image : Image) (s : MachineState)
    (h : s.canWrite image (.memory .qword {base := some .rbx, displacement := -8}) = true) : True := by
  simp only [rivet] at h
  guard_hyp h :ₛ permits image.writable (s.registers .rbx - 8#64) (s.registers .rbx - 8#64 + 8#64) = true
  trivial

end PlainConsumer
