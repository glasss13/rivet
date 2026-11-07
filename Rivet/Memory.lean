module
public import Rivet.Model
@[expose] public section
namespace Rivet

/-- Initial bytes and permissions for an address range. Bytes beyond `bytes.size`
up to `size` are zero-filled; bytes beyond `size` are ignored. -/
structure MemoryRegion where
  address : Nat
  size : Nat
  bytes : ByteArray
  readable : Bool
  writable : Bool

/-- Overlay regions on a supplied state. Regions replace both bytes and permissions;
outside them the state is unchanged. Later regions take precedence on overlap.
The ELF importer emits disjoint, bounded regions. This does not map OS pages or
set registers, the instruction pointer, or execution permissions. -/
def initializeMemory (regions : List MemoryRegion) (state : MachineState) : MachineState :=
  regions.foldl (fun state region =>
    let contains := fun address => region.address ≤ address && address < region.address + region.size
    { state with
      memory := fun address => if contains address then
        (region.bytes[address - region.address]?.getD 0).toFin else state.memory address
      readable := fun address => if contains address then region.readable else state.readable address
      writable := fun address => if contains address then region.writable else state.writable address }) state

end Rivet
