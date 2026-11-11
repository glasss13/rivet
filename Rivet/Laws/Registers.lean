module
public import Rivet.Interpreter.Machine
-- The register frame: which registers a stretch of execution may have written.
@[expose] public section
namespace Rivet

def MachineState.SameRegistersOutside (before after : MachineState) (written : List Reg) : Prop :=
  ∀ register, register ∉ written → after.registers register = before.registers register

theorem MachineState.SameRegistersOutside.refl {state : MachineState} {written : List Reg} :
    state.SameRegistersOutside state written :=
  fun _ _ => rfl

theorem MachineState.SameRegistersOutside.trans {first second third : MachineState} {written : List Reg}
    (earlier : first.SameRegistersOutside second written) (later : second.SameRegistersOutside third written) :
    first.SameRegistersOutside third written :=
  fun register outside => (later register outside).trans (earlier register outside)

theorem MachineState.SameRegistersOutside.mono {before after : MachineState} {written larger : List Reg}
    (agree : before.SameRegistersOutside after written) (covered : ∀ register ∈ written, register ∈ larger) :
    before.SameRegistersOutside after larger :=
  fun register outside => agree register (fun inside => outside (covered register inside))

end Rivet
