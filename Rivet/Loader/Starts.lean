module
public import Rivet.Loader.Exe
public import Rivet.Laws.Code
@[expose] public section
namespace Rivet

structure Starts (file : Exe) (layout : Layout) (stack : Region) (s : MachineState) : Prop where
  status : s.status = .running layout.entry
  access : ∀ segment ∈ layout.segments, ∀ address, segment.region.Contains address →
    s.kernel.access address =
      if segment.writable then .readWrite
      else if segment.executable then .readExec
      else .readOnly
  same : ∀ segment ∈ layout.segments, segment.bytes.Same (segment.memory file) s.memory
  apart : ∀ segment ∈ layout.segments, stack.Apart segment.region
  stackWrites : s.kernel.Writes stack
  stackPages : stack.base % 4096 = 0 ∧ stack.length % 4096 = 0
  rsp : stack.Contains (s.registers .rsp)
  aligned : (s.registers .rsp).toNat % 16 = 0

theorem Starts.reads {file : Exe} {layout : Layout} {stack : Region} {s : MachineState}
    (starts : Starts file layout stack s) (segment : Segment) (member : segment ∈ layout.segments) :
    s.kernel.Reads segment.region := by
  intro address inside
  have h := starts.access segment member address inside
  simp only [Kernel.readable, h]
  cases segment.writable <;> cases segment.executable <;> rfl

theorem Starts.writes {file : Exe} {layout : Layout} {stack : Region} {s : MachineState}
    (starts : Starts file layout stack s) (segment : Segment) (member : segment ∈ layout.segments)
    (writable : segment.writable = true) : s.kernel.Writes segment.region := by
  intro address inside
  have h := starts.access segment member address inside
  simp [Kernel.writable, h, writable, Access.writable]

theorem Starts.holds (starts : Starts file layout stack s) : s.Holds (file.code layout) := by
  intro address byte fetched
  unfold Exe.code at fetched
  split at fetched
  next segment found =>
    have checks := List.find?_some found
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at checks
    obtain ⟨⟨exec, ro⟩, bounds⟩ := checks
    have member := List.mem_of_find?_eq_some found
    have inside : segment.bytes.Contains address := by
      simpa only [Segment.bytes, Segment.region, Region.Contains, Region.part_base, Region.part_length,
        Region.root_base] using bounds
    have within := segment.inside
    have mapped : segment.region.Contains address := by
      simp only [Segment.region, Region.Contains, Region.root_base, Region.root_length]
      omega
    exact ⟨by simpa [exec, ro] using starts.access segment member address mapped,
      (starts.same segment member address inside).symm.trans (Option.some.inj fetched)⟩
  next => contradiction

end Rivet
