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
  | eax | edx
  deriving DecidableEq, Repr
@[simp] def Reg32.parent : Reg32 → Reg
  | .eax => .rax
  | .edx => .rdx
structure Mem8 where
  bytePtr ::
  base : Reg
  deriving DecidableEq, Repr
inductive Op where
  | xor (dst src : Reg32)
  | test (lhs rhs : Reg)
  | movzx (dst : Reg32) (src : Mem8)
  | add (dst src : Reg)
  | inc (dst : Reg)
  | dec (dst : Reg)
  | jz (target : Nat)
  | jnz (target : Nat)
  | ret
  deriving DecidableEq, Repr
/-- Whether an instruction can write a register, including RET advancing RSP. -/
def modifies : Op → Reg → Bool
  | .xor d _, r | .movzx d _, r => d.parent == r
  | .add d _, r | .inc d, r | .dec d, r => d == r
  | .ret, r => r == .rsp
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
