module
public import Rivet.Loader.Exe
public import Rivet.Interpreter.Machine
-- The state Linux starts a checked executable in.
@[expose] public section
namespace Rivet

-- What Linux guarantees of the state `s` it starts `file` in, for the `layout` the file was checked to
-- have and the pages `stack` Linux chose for its stack. The entry runs next. Each segment's pages are
-- mapped and readable, writable exactly if the segment is, and its own bytes are loaded. The stack is
-- mapped, readable, writable and apart from every segment, and `rsp` is in it, a multiple of 16. Linux
-- may map more (the vDSO), and the other registers and the flags may hold anything.
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

private theorem Segment.ascending_floor {floor : Nat} {segments : List Segment}
    (ascending : Segment.ascending floor segments = true) : ∀ segment ∈ segments, floor ≤ segment.start.toNat := by
  induction segments generalizing floor with
  | nil => simp
  | cons first rest inductionHypothesis =>
    simp only [Segment.ascending, Bool.and_eq_true, decide_eq_true_eq] at ascending
    intro segment member
    rcases List.mem_cons.mp member with rfl | member
    · exact ascending.1
    · have := inductionHypothesis ascending.2 segment member
      omega

private theorem Segment.ascending_apart {floor : Nat} {segments : List Segment}
    (ascending : Segment.ascending floor segments = true) :
    (segments.map Segment.region).Pairwise Region.Apart := by
  induction segments generalizing floor with
  | nil => simp
  | cons first rest inductionHypothesis =>
    simp only [Segment.ascending, Bool.and_eq_true, decide_eq_true_eq] at ascending
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨fun segment member => Or.inl ?_, inductionHypothesis ascending.2⟩
    have := Segment.ascending_floor ascending.2 segment member
    simpa only [Region.root_base, Region.root_length]

-- Two of a list of regions apart from each other are one region or apart.
private theorem Region.apart_of_pairwise {regions : List Region} (apart : regions.Pairwise Region.Apart) {a b : Region}
    (first : a ∈ regions) (second : b ∈ regions) : a = b ∨ a.Apart b := by
  induction regions with
  | nil => simp at first
  | cons head rest inductionHypothesis =>
    obtain ⟨each, others⟩ := List.pairwise_cons.mp apart
    rcases List.mem_cons.mp first with rfl | inRest <;> rcases List.mem_cons.mp second with rfl | alsoInRest
    · exact Or.inl rfl
    · exact Or.inr (each b alsoInRest)
    · exact Or.inr (each a inRest).symm
    · exact inductionHypothesis others inRest alsoInRest

-- A kernel made from regions apart from each other lets each be written exactly if the region says.
private theorem Kernel.ofRegions_writable {regions : List Region} (apart : regions.Pairwise Region.Apart) {r : Region}
    (member : r ∈ regions) {address : BitVec 64} (inside : r.Contains address) :
    (Kernel.ofRegions regions).writable address = r.writable := by
  cases writable : r.writable with
  | true => exact Kernel.writes_of_mem member writable address inside
  | false =>
    simp only [Kernel.ofRegions, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro other otherMember otherWritable otherInside
    rcases Region.apart_of_pairwise apart otherMember member with rfl | away
    · simp [writable] at otherWritable
    · simp only [Region.Apart, Region.Contains] at away inside otherInside
      omega

-- The memory that holds each segment's bytes.
private def Segment.load (file : Exe) : List Segment → Memory
  | [] => fun _ => 0
  | segment :: rest => fun address =>
    if segment.region.Contains address then segment.memory file address else Segment.load file rest address

private theorem Segment.load_same {file : Exe} {floor : Nat} {segments : List Segment}
    (ascending : Segment.ascending floor segments = true) :
    ∀ segment ∈ segments, segment.region.Same (segment.memory file) (Segment.load file segments) := by
  induction segments generalizing floor with
  | nil => simp
  | cons first rest inductionHypothesis =>
    simp only [Segment.ascending, Bool.and_eq_true, decide_eq_true_eq] at ascending
    intro segment member address inside
    rcases List.mem_cons.mp member with rfl | member
    · simp only [Segment.load, inside, ↓reduceIte]
    · have := Segment.ascending_floor ascending.2 segment member
      have outside : ¬first.region.Contains address := by
        simp only [Region.Contains, Region.root_base, Region.root_length] at inside ⊢
        omega
      simp only [Segment.load, outside, ↓reduceIte]
      exact inductionHypothesis ascending.2 segment member address inside

private theorem Exe.layout_ascending {file : Exe} {layout : Layout} (checked : file.layout = some layout) :
    Segment.ascending 4096 layout.segments = true := by
  simp only [Exe.layout] at checked
  split at checked
  · split at checked
    · split at checked
      · rename_i ordered
        cases checked
        exact ordered.1
      · cases checked
    · cases checked
  · cases checked

-- `Starts` holds of some state for every checked executable, so a theorem that assumes it says something.
theorem Starts.possible {file : Exe} {layout : Layout} (checked : file.layout = some layout) :
    ∃ stack s, Starts file layout stack s := by
  have ascending := Exe.layout_ascending checked
  let stack := Region.root 0#64 4096 true true
  let regions := stack :: layout.segments.map Segment.region
  have listed : ∀ segment ∈ layout.segments, segment.region ∈ regions :=
    fun segment member => List.mem_cons_of_mem _ (List.mem_map_of_mem member)
  have apart : ∀ segment ∈ layout.segments, stack.Apart segment.region := by
    intro segment member
    have := Segment.ascending_floor ascending segment member
    simp only [Region.Apart, stack, Region.root_base, Region.root_length]
    exact Or.inl this
  have pairwise : regions.Pairwise Region.Apart := by
    refine List.pairwise_cons.mpr ⟨fun r mapped => ?_, Segment.ascending_apart ascending⟩
    obtain ⟨segment, member, rfl⟩ := List.mem_map.mp mapped
    exact apart segment member
  let s : MachineState :=
    { registers := fun _ => 0, xmmRegisters := fun _ => 0, signFlag := false, zeroFlag := false, carryFlag := false,
      overflowFlag := false, memory := Segment.load file layout.segments, kernel := Kernel.ofRegions regions,
      status := .running layout.entry }
  refine ⟨stack, s, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, apart, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact fun segment member => Kernel.maps_of_mem (listed segment member)
  · exact fun segment member => Kernel.reads_of_mem (listed segment member) (Region.root_readable ..)
  · intro segment member address inside
    rw [Kernel.ofRegions_writable pairwise (listed segment member) inside, Region.root_writable]
  · intro segment member address inside
    refine Segment.load_same ascending segment member address ?_
    simp only [Region.Contains, Region.part_base, Region.part_length, Region.root_base, Region.root_length] at inside ⊢
    have := segment.inside
    omega
  · exact Kernel.maps_of_mem List.mem_cons_self
  · exact Kernel.reads_of_mem List.mem_cons_self (Region.root_readable ..)
  · exact Kernel.writes_of_mem List.mem_cons_self (Region.root_writable ..)
  · simp [stack, Region.root_base, Region.root_length]
  · simp [Region.Contains, stack, s, Region.root_base, Region.root_length]

end Rivet
