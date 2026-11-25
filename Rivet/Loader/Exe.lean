module
public import Rivet.Laws.Regions
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

-- Whole mapped pages `[start, start + length)`; contents are only guaranteed on `[start + skip, start + skip + size)`
-- because page padding varies across Linux versions.
structure Segment where
  start : BitVec 64
  length : Nat
  writable : Bool
  executable : Bool
  skip : Nat
  size : Nat
  fileOffset : Nat
  fileSize : Nat
  fits : start.toNat + length ≤ 2^64 := by decide
  inside : skip + size ≤ length := by decide
  deriving DecidableEq

abbrev Segment.region (segment : Segment) : Region :=
  Region.root segment.start segment.length true segment.writable segment.fits

abbrev Segment.bytes (segment : Segment) : Region :=
  segment.region.part segment.skip segment.size (by rw [Region.root_length]; exact segment.inside)

def Segment.memory (segment : Segment) (file : Exe) : Memory := fun address =>
  let index := (address - segment.start).toNat - segment.skip
  if index < segment.fileSize then Fin.ofNat 256 (file.u8 (segment.fileOffset + index)) else 0

def Segment.ascending (floor : Nat) : List Segment → Bool
  | [] => true
  | segment :: rest => floor ≤ segment.start.toNat && ascending (segment.start.toNat + segment.length) rest

structure ProgramHeader where
  type : Nat
  flags : Nat
  offset : Nat
  address : Nat
  fileSize : Nat
  size : Nat

def Exe.programHeader (file : Exe) (offset : Nat) : ProgramHeader where
  type := file.u32 offset
  flags := file.u32 (offset + 4)
  offset := file.u64 (offset + 8)
  address := file.u64 (offset + 16)
  fileSize := file.u64 (offset + 32)
  size := file.u64 (offset + 40)

abbrev ProgramHeader.executable (header : ProgramHeader) : Bool := header.flags.testBit 0
abbrev ProgramHeader.writable (header : ProgramHeader) : Bool := header.flags.testBit 1
abbrev ProgramHeader.readable (header : ProgramHeader) : Bool := header.flags.testBit 2

-- x86 without PKU makes W/X readable; Linux <6.7 can map empty PT_LOADs and skips zeroing RO BSS tails.
def ProgramHeader.segment (header : ProgramHeader) (fileSize : Nat) : Option Segment :=
  let start := BitVec.ofNat 64 (header.address / 4096 * 4096)
  let skip := header.address % 4096
  let length := (skip + header.size + 4095) / 4096 * 4096
  if checked : header.readable ∧ ¬(header.writable ∧ header.executable) ∧ 0 < header.size ∧
      (header.fileSize = header.size ∨ header.fileSize < header.size ∧ header.writable) ∧
      header.offset + header.fileSize ≤ fileSize ∧ header.offset % 4096 = skip ∧ start.toNat + length ≤ 2^64 then
    some { start, length, writable := header.writable, executable := header.executable, skip, size := header.size
           fileOffset := header.offset, fileSize := header.fileSize, fits := checked.2.2.2.2.2.2, inside := by omega }
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
          let first := segment.start.toNat + segment.skip
          segment.executable ∧ first ≤ entry ∧ entry < first + segment.fileSize) then
        some { entry := BitVec.ofNat 64 entry, segments }
      else none
    | none => none
  else none

end Rivet
