module
public import Rivet.Loader.Exe
public import Rivet.Interpreter.Machine
@[expose] public section
namespace Rivet

structure Starts (file : Exe) (layout : Layout) (stack : Region) (s : MachineState) : Prop where
  status : s.status = .running layout.entry
  access : ∀ segment ∈ layout.segments, ∀ address, segment.region.Contains address →
    s.kernel.access address = if segment.writable then .readWrite else .readOnly
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
  cases segment.writable <;> rfl

theorem Starts.writes {file : Exe} {layout : Layout} {stack : Region} {s : MachineState}
    (starts : Starts file layout stack s) (segment : Segment) (member : segment ∈ layout.segments)
    (writable : segment.writable = true) : s.kernel.Writes segment.region := by
  intro address inside
  have h := starts.access segment member address inside
  simp [Kernel.writable, h, writable, Access.writable]

end Rivet
