module
public import Rivet.Laws.Regions
public import Rivet.Interpreter.Decode
@[expose] public section
namespace Rivet

-- 4096-byte little-endian base-256 pages (one big Nat parses quadratically in Lean).
structure Exe where
  size : Nat
  pages : List Nat

def Exe.u8 (file : Exe) (offset : Nat) : Nat :=
  (file.pages.getD (offset / 4096) 0 >>> (8 * (offset % 4096))) % 256

def Exe.u16 (file : Exe) (offset : Nat) : Nat := file.u8 offset + 2^8 * file.u8 (offset + 1)

def Exe.u32 (file : Exe) (offset : Nat) : Nat := file.u16 offset + 2^16 * file.u16 (offset + 2)

def Exe.u64 (file : Exe) (offset : Nat) : Nat := file.u32 offset + 2^32 * file.u32 (offset + 4)

-- One ELF `PT_LOAD` segment (`vaddr`, `memsz`, `offset`, `filesz` match `Elf64_Phdr`).
-- Permissions apply to whole 4 KiB pages (`region`); contents only to `[vaddr, vaddr + memsz)` (`bytes`).
structure Segment where
  vaddr : BitVec 64
  memsz : Nat
  offset : Nat
  filesz : Nat
  writable : Bool
  executable : Bool
  fits : vaddr.toNat / 4096 * 4096 + (vaddr.toNat % 4096 + memsz + 4095) / 4096 * 4096 ≤ 2^64 := by decide
  deriving DecidableEq

abbrev Segment.mapStart (segment : Segment) : BitVec 64 :=
  BitVec.ofNat 64 (segment.vaddr.toNat / 4096 * 4096)

abbrev Segment.mapSize (segment : Segment) : Nat :=
  (segment.vaddr.toNat % 4096 + segment.memsz + 4095) / 4096 * 4096

theorem Segment.mapStart_toNat (segment : Segment) : segment.mapStart.toNat = segment.vaddr.toNat / 4096 * 4096 := by
  have := segment.vaddr.isLt
  simp only [Segment.mapStart, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

abbrev Segment.region (segment : Segment) : Region :=
  Region.root segment.mapStart segment.mapSize true segment.writable (by
    rw [Segment.mapStart_toNat]; exact segment.fits)

abbrev Segment.bytes (segment : Segment) : Region :=
  segment.region.part (segment.vaddr.toNat % 4096) segment.memsz (by rw [Region.root_length, Segment.mapSize]; omega)

def Segment.memory (segment : Segment) (file : Exe) : Memory := fun address =>
  let index := (address - segment.vaddr).toNat
  if index < segment.filesz then Fin.ofNat 256 (file.u8 (segment.offset + index)) else 0

def Segment.ascending (floor : Nat) : List Segment → Bool
  | [] => true
  | segment :: rest =>
    let start := segment.vaddr.toNat / 4096 * 4096
    floor ≤ start && ascending (start + segment.mapSize) rest

structure ProgramHeader where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat

def Exe.programHeader (file : Exe) (offset : Nat) : ProgramHeader where
  type := file.u32 offset
  flags := file.u32 (offset + 4)
  offset := file.u64 (offset + 8)
  vaddr := file.u64 (offset + 16)
  filesz := file.u64 (offset + 32)
  memsz := file.u64 (offset + 40)

abbrev ProgramHeader.executable (header : ProgramHeader) : Bool := header.flags.testBit 0
abbrev ProgramHeader.writable (header : ProgramHeader) : Bool := header.flags.testBit 1
abbrev ProgramHeader.readable (header : ProgramHeader) : Bool := header.flags.testBit 2

-- x86 without PKU makes W/X readable; Linux <6.7 can map empty PT_LOADs and skips zeroing RO BSS tails.
def ProgramHeader.segment (header : ProgramHeader) (fileSize : Nat) : Option Segment :=
  let vaddr := BitVec.ofNat 64 header.vaddr
  let pageOffset := header.vaddr % 4096
  let mapStart := header.vaddr / 4096 * 4096
  let mapSize := (pageOffset + header.memsz + 4095) / 4096 * 4096
  if checked : header.readable ∧ ¬(header.writable ∧ header.executable) ∧ 0 < header.memsz ∧
      (header.filesz = header.memsz ∨ header.filesz < header.memsz ∧ header.writable) ∧
      header.offset + header.filesz ≤ fileSize ∧ header.offset % 4096 = pageOffset ∧
      header.vaddr < 2^64 ∧ mapStart + mapSize ≤ 2^64 then
    some { vaddr, memsz := header.memsz, offset := header.offset, filesz := header.filesz,
           writable := header.writable, executable := header.executable,
           fits := by
             have hlt : header.vaddr < 2^64 := checked.2.2.2.2.2.2.1
             have hfit : mapStart + mapSize ≤ 2^64 := checked.2.2.2.2.2.2.2
             simpa only [vaddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using hfit }
  else none

structure Layout where
  entry : BitVec 64
  segments : List Segment
  deriving DecidableEq

-- Linux caps phdrs at 4096 bytes; Linux <5.8 defaults missing PT_GNU_STACK to exec;
-- Linux <6.7 skips zeroing out-of-order segments.
def Exe.layout (file : Exe) : Option Layout :=
  let count := file.u16 56
  let headers := (List.range count).map fun index => file.programHeader (file.u64 32 + 56 * index)
  let loads := headers.filter fun header => header.type = 1
  if 64 ≤ file.size ∧ file.u32 0 = 0x464c457f ∧ file.u8 4 = 2 ∧ file.u8 5 = 1 ∧ file.u8 6 = 1 ∧
      file.u16 16 = 2 ∧ file.u16 18 = 62 ∧ file.u32 20 = 1 ∧ file.u16 54 = 56 ∧
      56 * count ≤ 4096 ∧ file.u64 32 + 56 * count ≤ file.size ∧
      headers.all (fun header => header.type ≠ 2 ∧ header.type ≠ 3 ∧
        (header.type = 0x6474e551 → ¬header.executable)) ∧
      headers.any (fun header => header.type = 0x6474e551) then
    match loads.mapM fun header => header.segment file.size with
    | some segments =>
      let entry := file.u64 24
      if Segment.ascending 4096 segments ∧ segments.any (fun segment =>
          segment.executable ∧ segment.vaddr.toNat ≤ entry ∧ entry < segment.vaddr.toNat + segment.filesz) then
        some { entry := BitVec.ofNat 64 entry, segments }
      else none
    | none => none
  else none

def Exe.code (file : Exe) (layout : Layout) : Code := fun address =>
  -- Compute the byte bounds directly: Region.root and Region.part are sealed for proof automation.
  match layout.segments.find? fun s =>
      s.executable && !s.writable && decide (s.vaddr.toNat ≤ address.toNat ∧ address.toNat < s.vaddr.toNat + s.memsz) with
  | some segment => some (segment.memory file address)
  | none => none

end Rivet
