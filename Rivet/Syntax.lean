module
public import Std
@[expose] public section
namespace Rivet
def word : Nat := 2^64
inductive Reg where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr
-- Widths are expressed by x86 register aliases and the memory operand type.
inductive Reg32 where
  | eax | ebx | ecx | edx | esi | edi | ebp | esp
  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
  deriving DecidableEq, Repr
@[simp] def Reg32.parent : Reg32 → Reg
  | .eax => .rax
  | .ebx => .rbx
  | .ecx => .rcx
  | .edx => .rdx
  | .esi => .rsi
  | .edi => .rdi
  | .ebp => .rbp
  | .esp => .rsp
  | .r8d => .r8
  | .r9d => .r9
  | .r10d => .r10
  | .r11d => .r11
  | .r12d => .r12
  | .r13d => .r13
  | .r14d => .r14
  | .r15d => .r15

/-- Low-byte aliases; legacy high-byte registers are not supported. -/
inductive Reg8 where
  | al | bl | cl | dl | sil | dil | bpl | spl | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
  deriving DecidableEq, Repr
@[simp] def Reg8.parent : Reg8 → Reg
  | .al => .rax
  | .bl => .rbx
  | .cl => .rcx
  | .dl => .rdx
  | .sil => .rsi
  | .dil => .rdi
  | .bpl => .rbp
  | .spl => .rsp
  | .r8b => .r8
  | .r9b => .r9
  | .r10b => .r10
  | .r11b => .r11
  | .r12b => .r12
  | .r13b => .r13
  | .r14b => .r14
  | .r15b => .r15
structure Mem8 where
  bytePtr ::
  base : Reg
  deriving DecidableEq, Repr
inductive Op where
  | xor (destination source : Reg32)
  | test (left right : Reg)
  | movzx (destination : Reg32) (source : Mem8)
  | mov (destination source : Reg)
  | store8 (destination : Mem8) (source : Reg8)
  | cmp (left right : Reg)
  | add (destination source : Reg)
  | inc (destination : Reg)
  | dec (destination : Reg)
  | jb (target : Nat)
  | jz (target : Nat)
  | jnz (target : Nat)
  | ret
  deriving DecidableEq, Repr
/-- Whether an instruction can write a register, including RET advancing RSP. -/
def modifies : Op → Reg → Bool
  | .xor destination _, register | .movzx destination _, register => destination.parent == register
  | .mov destination _, register | .add destination _, register | .inc destination, register | .dec destination, register => destination == register
  | .ret, register => register == .rsp
  | _, _ => false

structure Instruction where
  op : Op
  line : Nat
  deriving DecidableEq, Repr
abbrev Program := List Instruction
structure Access where
  address : Nat
  size : Nat
  deriving DecidableEq, Repr
end Rivet
