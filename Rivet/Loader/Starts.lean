module
public import Rivet.Loader.Exe
public import Rivet.Interpreter.Machine
-- The state Linux starts a checked executable in.
@[expose] public section
namespace Rivet

-- The start state `s` of a checked executable `file` with `layout`, given a launch whose `stack` pages
-- are placed apart from every segment. The entry runs next. Each segment's pages are mapped and readable,
-- writable exactly if the segment is, and its own bytes are loaded. The stack is mapped, readable,
-- writable, and `rsp` is in it, a multiple of 16. Extra mappings (e.g. vDSO), other registers, and flags
-- are left unconstrained.
structure Starts (file : Exe) (layout : Layout) (stack : Region) (s : MachineState) : Prop where
  status : s.status = .running layout.entry
  maps : ∀ segment ∈ layout.segments, s.kernel.Maps segment.region
  reads : ∀ segment ∈ layout.segments, s.kernel.Reads segment.region
  writable : ∀ segment ∈ layout.segments, ∀ address, segment.region.Contains address →
    s.kernel.writable address = segment.writable
  same : ∀ segment ∈ layout.segments, segment.bytes.Same (segment.memory file) s.memory
  apart : ∀ segment ∈ layout.segments, stack.Apart segment.region
  stackMaps : s.kernel.Maps stack
  stackReads : s.kernel.Reads stack
  stackWrites : s.kernel.Writes stack
  stackPages : stack.base % 4096 = 0 ∧ stack.length % 4096 = 0
  rsp : stack.Contains (s.registers .rsp)
  aligned : (s.registers .rsp).toNat % 16 = 0

theorem Starts.writes {file : Exe} {layout : Layout} {stack : Region} {s : MachineState}
    (starts : Starts file layout stack s) (segment : Segment) (member : segment ∈ layout.segments)
    (writable : segment.writable = true) : s.kernel.Writes segment.region :=
  fun address inside => (starts.writable segment member address inside).trans writable

end Rivet
