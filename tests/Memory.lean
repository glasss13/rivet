import Rivet

namespace Rivet.MemoryRegression

-- The previous implementations are kept only here to check semantic equivalence.
private def oldStoreByte (memory : Memory) (address : Nat) (value : Fin 256) : Memory :=
  { regions := memory.regions.map (fun region => { region with contents := fun offset =>
      if region.address + offset = address then value else region.contents offset })
    valid := by
      have preserve (regions : List MemoryRegion) :
          MemoryRegion.validLayout (regions.map (fun region => { region with contents := fun offset =>
            if region.address + offset = address then value else region.contents offset })) =
            MemoryRegion.validLayout regions := by
        induction regions with
        | nil => rfl
        | cons region rest ih =>
          simp only [List.map_cons, MemoryRegion.validLayout, ih]
          simp [List.all_map, Function.comp_def]
      rw [preserve]
      exact memory.valid }

private theorem storeZero (memory : Memory) (address : Nat) (bytes : Nat → Fin 256) :
    memory.storeBytes address 0 bytes = memory := by
  have empty (n : Nat) : ¬ (address ≤ n ∧ n < address) := by omega
  simp [Memory.storeBytes, empty]

private theorem storeSucc (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    oldStoreByte (memory.storeBytes address size bytes) (address + size) (bytes size) =
      memory.storeBytes address (size + 1) bytes := by
  unfold oldStoreByte Memory.storeBytes
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro region member
  congr 1
  funext offset
  by_cases last : region.address + offset = address + size
  · simp [last]
  · have notLast : region.address + offset - address ≠ size ∨ region.address + offset < address := by omega
    by_cases inside : address ≤ region.address + offset ∧ region.address + offset < address + size
    · have larger : address ≤ region.address + offset ∧ region.address + offset < address + (size + 1) := by omega
      simp [last, inside, larger]
    · have larger : ¬ (address ≤ region.address + offset ∧ region.address + offset < address + (size + 1)) := by omega
      simp [last, inside, larger]

-- Equality holds for arbitrary regions, including unmapped/readonly locations,
-- and for all region contents, not merely the bytes exposed by Memory.read.
private theorem store_eq_old_fold (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    memory.storeBytes address size bytes =
      (List.range size).foldl (fun current offset => oldStoreByte current (address + offset) (bytes offset)) memory := by
  induction size with
  | zero => simpa using storeZero memory address bytes
  | succ size ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← ih, storeSucc]

private theorem byteFoldBound (memory : Nat → Fin 256) (address : Nat) (offsets : List Nat) :
    offsets.foldr (fun offset value => (memory (address + offset)).val + 256 * value) 0 <
      256 ^ offsets.length := by
  induction offsets with
  | nil => simp
  | cons offset rest ih =>
    have byteBound := (memory (address + offset)).isLt
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    omega

-- The old natural-number return-address read did not reduce modulo 2^64.
-- The bound proves that replacing it by the typed byte read cannot truncate it.
theorem returnAddress_eq_legacy (memory : Nat → Fin 256) (address : Nat) :
    (readBytes memory address 8).toNat =
      (List.range 8).foldr (fun offset value => (memory (address + offset)).val + 256 * value) 0 := by
  apply Nat.mod_eq_of_lt
  simpa using byteFoldBound memory address (List.range 8)

-- Any byte count, including scalar zero-extension and wider reads truncated to 64 bits.
theorem scalarRead_eq_legacy (memory : Nat → Fin 256) (address size : Nat) :
    (readBytes memory address size).setWidth 64 =
      BitVec.ofNat 64 ((List.range size).foldr
        (fun offset value => (memory (address + offset)).val + 256 * value) 0) := by
  have bound := byteFoldBound memory address (List.range size)
  apply BitVec.eq_of_toNat_eq
  simp only [readBytes, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have fit : (List.range size).foldr
      (fun offset value => (memory (address + offset)).val + 256 * value) 0 < 2 ^ (8 * size) := by
    simpa [Nat.pow_mul] using bound
  rw [Nat.mod_eq_of_lt fit]

-- SIMD loads are the same byte decoding with a larger size.
example (memory : Nat → Fin 256) (address : Nat) :
    readBytes memory address 16 = BitVec.ofNat 128 ((List.range 16).foldr
      (fun offset value => (memory (address + offset)).val + 256 * value) 0) := rfl

private def oldWriteMemory (state : MachineState) (address : Nat) (width : Width) (value : BitVec 64) : MachineState :=
  (List.range width.bytes).foldl (fun current offset =>
    {current with memory := (oldStoreByte current.memory (address + offset)
      ⟨value.toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩)}) state

-- Equality of whole states validates the change from state folds to memory updates.
theorem scalarWrite_eq_legacy (state : MachineState) (address : Nat) (width : Width) (value : BitVec 64) :
    state.writeMemory address width value = oldWriteMemory state address width value := by
  have fold (offsets : List Nat) (current : MachineState) :
      offsets.foldl (fun accumulated offset =>
        {accumulated with memory := (oldStoreByte accumulated.memory (address + offset)
          ⟨value.toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩)}) current =
      {current with memory := offsets.foldl (fun memory offset => oldStoreByte memory (address + offset)
        ⟨value.toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩) current.memory} := by
    induction offsets generalizing current with
    | nil => rfl
    | cons offset rest ih =>
      simpa only [List.foldl_cons] using ih _
  rw [oldWriteMemory, fold]
  simp only [MachineState.writeMemory, store_eq_old_fold]

-- Scalar writes leave every non-memory field definitionally unchanged.
example (state : MachineState) (address : Nat) (width : Width) (value : BitVec 64) :
    (state.writeMemory address width value).registers = state.registers := rfl

-- Empty stores and outside bytes require no mapping or permission assumptions.
example (memory : Memory) (address : Nat) (bytes : Nat → Fin 256) :
    memory.storeBytes address 0 bytes = memory := storeZero memory address bytes
example (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) (other : Nat)
    (outside : other < address ∨ address + size ≤ other) :
    (memory.storeBytes address size bytes) other = memory other :=
  memory.read_storeBytes_outside address size bytes other outside

-- Raw stores update mapped readonly bytes; instruction permission checks remain separate.
private def readonlyMemory : Memory :=
  ⟨[{address := 32, size := 4, readable := true, writable := false}], by decide +kernel⟩
example : (readonlyMemory.storeBytes 33 2 (fun _ => 17)) 33 = 17 := by decide +kernel
example : (readonlyMemory.storeBytes 33 2 (fun _ => 17)).writable 33 = false := by decide +kernel
example : (readonlyMemory.storeBytes 0 64 (fun _ => 17)) 0 = 0 := by decide +kernel
example : permits readonlyMemory.writable 33 2 = false := by decide +kernel

-- The complete access must fit: the last byte is valid, crossing the boundary is not.
example : permits (fun _ => true) (word - 1) 1 = true := by decide +kernel
example : permits (fun _ => true) (word - 1) 2 = false := by decide +kernel
example : readBytes (fun _ => 255) 0 0 = 0 := by decide +kernel

-- A denied multi-byte store faults without committing any memory, register or flag update.
example (state : MachineState) (destination : Address) (source : Reg) (pc : Nat) (flags : FlagValues)
    (denied : permits state.writable (destination.evaluate state.registers).toNat 8 = false) :
    stepOp (.mov (.memory .qword destination) (.reg64 source)) pc state flags =
      {state with status := .fault} := by
  simp [stepOp, MachineState.canWrite, Width.bytes, denied]

#print axioms returnAddress_eq_legacy
#print axioms scalarRead_eq_legacy
#print axioms scalarWrite_eq_legacy

end Rivet.MemoryRegression
