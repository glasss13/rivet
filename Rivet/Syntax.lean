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
  | xor (destination source : Reg32)
  | test (left right : Reg)
  | movzx (destination : Reg32) (source : Mem8)
  | add (destination source : Reg)
  | inc (destination : Reg)
  | dec (destination : Reg)
  | jz (target : Nat)
  | jnz (target : Nat)
  | ret
  deriving DecidableEq, Repr
/-- Whether an instruction can write a register, including RET advancing RSP. -/
def modifies : Op → Reg → Bool
  | .xor destination _, register | .movzx destination _, register => destination.parent == register
  | .add destination _, register | .inc destination, register | .dec destination, register => destination == register
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
