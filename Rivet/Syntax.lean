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
  | al | bl | cl | dl | sil | dil | bpl | spl | r8l | r9l | r10l | r11l | r12l | r13l | r14l | r15l
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
  | .r8l => .r8
  | .r9l => .r9
  | .r10l => .r10
  | .r11l => .r11
  | .r12l => .r12
  | .r13l => .r13
  | .r14l => .r14
  | .r15l => .r15
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

/-- The sixteen legacy 128-bit XMM registers available in 64-bit mode. -/
inductive Xmm where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr

inductive XmmMove where
  | movups | movdqu
  deriving DecidableEq, Repr

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

/-- Scalar operations sharing the same width and operand rules. -/
inductive BinaryOp where
  | add | sub | sbb | cmp | test | and | or | xor
  deriving DecidableEq, Repr

def BinaryOp.writes : BinaryOp → Bool
  | .cmp | .test => false
  | _ => true

/-- 64-bit arithmetic immediates are sign-extended from 32 bits. TEST has no register/memory form. -/
def validBinary (operation : BinaryOp) (destination source : Operand) : Bool :=
  validMove destination source &&
    (match destination.width, source with
    | some .qword, .immediate value => -(2^31) ≤ value && value < 2^31
    | _, _ => true) &&
    (match operation, source with | .test, .memory _ _ => false | _, _ => true)

/-- Conditions supported by the modeled zero, carry, and sign flags. -/
inductive Condition where
  | equal | notEqual | below | aboveOrEqual | belowOrEqual | above | sign
  deriving DecidableEq, Repr

def validConditionalMove (destination source : Operand) : Bool :=
  match destination with
  | .reg16 _ | .reg32 _ | .reg64 _ => source.width == destination.width
  | _ => false

/-- Truncating two/three-operand IMUL: a 16/32/64-bit register, matching
register/memory source, and optionally an encodable immediate multiplier. -/
def validImul (destination source : Operand) (immediate : Option Int) : Bool :=
  validConditionalMove destination source &&
    match immediate with
    | none => true
    | some value => validBinary .add destination (.immediate value)

inductive ShiftOp where
  | shl | shr
  deriving DecidableEq, Repr

/-- The immediate-count register forms needed by LZ4. -/
def validShift (destination : Operand) (count : Nat) : Bool :=
  (match destination with | .reg32 _ | .reg64 _ => true | _ => false) && count < 256

inductive Op where
  | nop
  | movd (destination : Xmm) (source : Reg32)
  | pshufd (destination source : Xmm) (order : Nat)
  | loadXmm (operation : XmmMove) (destination : Xmm) (source : Address)
  | storeXmm (operation : XmmMove) (destination : Address) (source : Xmm)
  | binary (operation : BinaryOp) (destination source : Operand)
  | lea (destination : Reg) (source : Address)
  | movzx (destination : Reg32) (source : Operand)
  | movsxd (destination : Reg) (source : Operand)
  | mov (destination source : Operand)
  | shift (operation : ShiftOp) (destination : Operand) (count : Nat)
  | imul (destination source : Operand) (immediate : Option Int)
  | not (destination : Operand)
  | inc (destination : Reg)
  | dec (destination : Reg)
  | jmp (target : Nat)
  | jcc (condition : Condition) (target : Nat)
  | setcc (condition : Condition) (destination : Operand)
  | cmovcc (condition : Condition) (destination source : Operand)
  | push (source : Reg)
  | pop (destination : Reg)
  | call (target : Nat)
  | ret
  deriving DecidableEq, Repr
/-- Whether an instruction can write a register, including implicit RSP updates. -/
def modifies : Op → Reg → Bool
  | .movzx destination _, register => destination.parent == register
  | .binary operation destination _, register => operation.writes && destination.register == some register
  | .shift _ destination _, register | .imul destination _ _, register
  | .not destination, register | .mov destination _, register | .setcc _ destination, register
  | .cmovcc _ destination _, register => destination.register == some register
  | .lea destination _, register | .movsxd destination _, register
  | .inc destination, register | .dec destination, register => destination == register
  | .pop destination, register => register == .rsp || destination == register
  | .push _, register | .call _, register | .ret, register => register == .rsp
  | _, _ => false

structure Instruction where
  address : Nat
  length : Nat
  op : Op
  deriving DecidableEq, Repr
abbrev Program := List Instruction

/-- Fetch at an exact byte address. Invalid addresses or x86 instruction lengths do not execute. -/
def Program.fetch (program : Program) (address : Nat) : Option Instruction :=
  program.find? fun instruction => instruction.address == address && address < word &&
    0 < instruction.length && instruction.length ≤ 15

/-- The byte address following an instruction, with 64-bit address arithmetic. -/
def Program.nextAddress (program : Program) (address : Nat) : Nat :=
  ((program.fetch address).map fun instruction => (address + instruction.length) % word).getD address
structure Access where
  address : Nat
  size : Nat
  deriving DecidableEq, Repr
end Rivet
