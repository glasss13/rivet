module
public import Rivet.Laws.Regions
-- An executable file's bytes, and the check that Linux loads it in one way: `Exe.layout`.
@[expose] public section
namespace Rivet

-- A file of `size` bytes, 4096 to a page: byte `i` of a page is digit `i`, base 256, of its number.
-- A read shifts one page, not the file; and Lean parses pages in seconds, where one number for a large
-- file takes minutes.
structure Exe where
  size : Nat
  pages : List Nat

-- The byte at `offset`, and the little-endian numbers of 2, 4 and 8 bytes there.
def Exe.u8 (file : Exe) (offset : Nat) : Nat :=
  (file.pages.getD (offset / 4096) 0 >>> (8 * (offset % 4096))) % 256

def Exe.u16 (file : Exe) (offset : Nat) : Nat := file.u8 offset + 2^8 * file.u8 (offset + 1)

def Exe.u32 (file : Exe) (offset : Nat) : Nat := file.u16 offset + 2^16 * file.u16 (offset + 2)

def Exe.u64 (file : Exe) (offset : Nat) : Nat := file.u32 offset + 2^32 * file.u32 (offset + 4)

-- A loadable segment as Linux maps it: whole pages, `length` bytes from `start`, all readable. Its own
-- bytes are the `size` bytes `skip` into them: the first `fileSize` are the file's from `fileOffset`, and
-- the rest are zero. What the pages hold around its own bytes varies with the kernel's version.
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

-- The pages Linux maps for the segment.
abbrev Segment.region (segment : Segment) : Region :=
  Region.root segment.start segment.length true segment.writable segment.fits

-- The segment's own bytes.
abbrev Segment.bytes (segment : Segment) : Region :=
  segment.region.part segment.skip segment.size (by rw [Region.root_length]; exact segment.inside)

-- What the loader leaves in the segment's own bytes.
def Segment.memory (segment : Segment) (file : Exe) : Memory := fun address =>
  let index := (address - segment.start).toNat - segment.skip
  if index < segment.fileSize then Fin.ofNat 256 (file.u8 (segment.fileOffset + index)) else 0

-- Each segment's pages start at or after `floor`, and at or after the end of the segment before.
def Segment.ascending (floor : Nat) : List Segment → Bool
  | [] => true
  | segment :: rest => floor ≤ segment.start.toNat && ascending (segment.start.toNat + segment.length) rest

-- A program header, as the file holds it.
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

-- The segment a `PT_LOAD` header asks for, or `none` if Linux would not map it, or not the same way on
-- every kernel and machine:
-- - It is readable. A page that can be written can be read on x86, and one that can only be run can
--   be read on a machine without protection keys.
-- - It is not both writable and executable.
-- - It has bytes. Linux before 6.7 can map a page for a segment with none.
-- - Bytes past the file's need it writable. Linux maps the pages past the file's writable whatever the
--   header says, and before 6.7 leaves the file's bytes where it cannot write zeroes.
-- - The file holds its bytes, at an offset that is its address modulo a page, as mapping the file needs.
-- - Its pages end by 2^64.
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

-- Where a checked executable's segments are, and its first instruction.
structure Layout where
  entry : BitVec 64
  segments : List Segment
  deriving DecidableEq

-- The layout of a static, fixed-address x86-64 Linux executable, or `none` if it fails the modeled
-- ELF checks:
-- - It is ELF64, little-endian, version 1, `ET_EXEC`, `EM_X86_64`, and its program headers fit in
--   one 4096-byte page (Linux's `binfmt_elf.c` limit) and within the file.
-- - No header is `PT_DYNAMIC` or `PT_INTERP`.
-- - A `PT_GNU_STACK` header is there and none is executable. Without one, Linux before 5.8 makes the
--   stack and every readable page executable.
-- - Every `PT_LOAD` header is a segment.
-- - The segments' pages ascend in header order, from the second page on, so no two share a page. Linux
--   before 6.7 does not zero-fill a segment below an earlier one.
-- - The entry is one of the file's bytes in an executable segment.
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
