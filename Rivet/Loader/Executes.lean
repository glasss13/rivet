module
public import Rivet.Loader.Starts
public import Rivet.Laws.Block
import all Rivet.Laws.Block
@[expose] public section
namespace Rivet

private theorem Starts.holds (starts : Starts file layout stack s) : s.Holds (file.code layout) := by
  intro address byte fetched
  unfold Exe.code at fetched
  split at fetched
  next segment found =>
    have checks := List.find?_some found
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at checks
    obtain ⟨⟨exec, ro⟩, bounds⟩ := checks
    have member := List.mem_of_find?_eq_some found
    have inside : segment.bytes.Contains address := by
      simp only [Segment.bytes, Segment.region, Region.Contains, Region.part_base,
        Region.part_length, Region.root_base, Segment.mapStart_toNat]
      omega
    have mapped : segment.region.Contains address := by
      simp only [Segment.region, Segment.mapSize, Region.Contains, Region.root_base,
        Region.root_length, Segment.mapStart_toNat]
      omega
    exact ⟨by simpa [exec, ro] using starts.access segment member address mapped,
      (starts.same segment member address inside).symm.trans (Option.some.inj fetched)⟩
  next => contradiction

def Executes (file : Exe) (Q : MachineState → MachineState → Prop) : Prop :=
  ∃ layout, file.layout = some layout ∧
    ∀ stack s, Starts file layout stack s →
      ∀ choices : FlagChoices, ∃ steps, Q s (execute steps s choices)

theorem Executes.ofBlock {file : Exe} {layout : Layout} {Q : MachineState → MachineState → Prop}
    (valid : file.layout = some layout)
    (proof : ∀ stack s, Starts file layout stack s → Block (file.code layout) s .all (Q s)) :
    Executes file Q :=
  ⟨layout, valid, fun stack s starts choices =>
    have ⟨_, ⟨steps, reached⟩, _, post⟩ := (proof stack s starts).allChoices starts.holds choices
    ⟨steps, reached ▸ post⟩⟩

end Rivet
