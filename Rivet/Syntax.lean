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
inductive Reg16 where
  | ax | bx | cx | dx | si | di | bp | sp | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w
  deriving DecidableEq, Repr
@[simp] def Reg16.parent : Reg16 → Reg
  | .ax => .rax
  | .bx => .rbx
  | .cx => .rcx
  | .dx => .rdx
  | .si => .rsi
  | .di => .rdi
  | .bp => .rbp
  | .sp => .rsp
  | .r8w => .r8
  | .r9w => .r9
  | .r10w => .r10
  | .r11w => .r11
  | .r12w => .r12
  | .r13w => .r13
  | .r14w => .r14
  | .r15w => .r15

inductive Width where
  | byte | word | dword | qword
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .byte => 1 | .word => 2 | .dword => 4 | .qword => 8

def Width.bits (width : Width) : Nat := 8 * width.bytes

inductive Scale where
  | one | two | four | eight
  deriving DecidableEq, Repr

def Scale.value : Scale → Nat
  | .one => 1 | .two => 2 | .four => 4 | .eight => 8

/-- A 64-bit effective address; displacement is signed and arithmetic wraps. -/
structure Address where
  base : Option Reg := none
  index : Option Reg := none
  scale : Scale := .one
  displacement : Int := 0
  deriving DecidableEq, Repr

def Address.baseOnly (register : Reg) : Address := { base := some register }

inductive Operand where
  | reg8 (register : Reg8)
  | reg16 (register : Reg16)
  | reg32 (register : Reg32)
  | reg64 (register : Reg)
  | memory (width : Width) (address : Address)
  | immediate (value : Int)
  deriving DecidableEq, Repr

def Operand.width : Operand → Option Width
  | .reg8 _ => some .byte | .reg16 _ => some .word
  | .reg32 _ => some .dword | .reg64 _ => some .qword
  | .memory width _ => some width | .immediate _ => none

def Operand.register : Operand → Option Reg
  | .reg8 register => some register.parent | .reg16 register => some register.parent
  | .reg32 register => some register.parent | .reg64 register => some register
  | _ => none

/-- MOV requires equal widths, no memory-to-memory transfer, and an encodable immediate. -/
def validMove (destination source : Operand) : Bool :=
  match destination.width with
  | none => false
  | some width =>
    match destination, source with
    | .memory _ _, .memory _ _ => false
    | .memory .qword _, .immediate value => -(2^31) ≤ value && value < 2^31
    | _, .immediate value => -(2^(width.bits-1)) ≤ value && value < 2^width.bits
    | _, _ => source.width == some width

inductive Op where
  | xor (destination source : Reg32)
  | test (left right : Reg)
  | lea (destination : Reg) (source : Address)
  | movzx (destination : Reg32) (source : Operand)
  | movsxd (destination : Reg) (source : Operand)
  | mov (destination source : Operand)
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
  | .mov destination _, register => destination.register == some register
  | .lea destination _, register | .movsxd destination _, register
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
