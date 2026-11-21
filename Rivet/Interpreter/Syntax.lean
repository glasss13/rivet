module
public import Std
-- Instruction syntax: registers, operands, operations, and programs.
@[expose] public section
namespace Rivet
inductive Reg where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq
-- Widths are expressed by x86 register aliases and the memory operand type.
inductive Reg32 where
  | eax | ebx | ecx | edx | esi | edi | ebp | esp
  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
  deriving DecidableEq
def Reg32.parent : Reg32 → Reg
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

inductive Reg8 where
  | al | bl | cl | dl | sil | dil | bpl | spl | r8l | r9l | r10l | r11l | r12l | r13l | r14l | r15l
  deriving DecidableEq
def Reg8.parent : Reg8 → Reg
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
  deriving DecidableEq
def Reg16.parent : Reg16 → Reg
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

inductive Xmm where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq

inductive XmmMove where
  | movups | movdqu
  deriving DecidableEq

inductive Width where
  | byte | word | dword | qword
  deriving DecidableEq

@[simp] abbrev Width.bytes : Width → Nat
  | .byte => 1 | .word => 2 | .dword => 4 | .qword => 8

@[simp] abbrev Width.bits : Width → Nat
  | .byte => 8 | .word => 16 | .dword => 32 | .qword => 64

inductive Scale where
  | one | two | four | eight
  deriving DecidableEq

def Scale.value : Scale → Nat
  | .one => 1 | .two => 2 | .four => 4 | .eight => 8

structure Address where
  base : Option Reg := none
  index : Option Reg := none
  scale : Scale := .one
  displacement : Int := 0
  deriving DecidableEq

inductive Operand where
  | reg8 (register : Reg8)
  | reg16 (register : Reg16)
  | reg32 (register : Reg32)
  | reg64 (register : Reg)
  | memory (width : Width) (address : Address)
  | immediate (value : Int)
  deriving DecidableEq

abbrev Operand.width : Operand → Option Width
  | .reg8 _ => some .byte | .reg16 _ => some .word
  | .reg32 _ => some .dword | .reg64 _ => some .qword
  | .memory width _ => some width | .immediate _ => none

def validMove (destination source : Operand) : Bool :=
  match destination.width with
  | none => false
  | some width =>
    match destination, source with
    | .memory _ _, .memory _ _ => false
    | .memory .qword _, .immediate value => -(2^31) ≤ value && value < 2^31
    | _, .immediate value => -(2^(width.bits-1)) ≤ value && value < 2^width.bits
    | _, _ => source.width == some width

inductive BinaryOp where
  | add | sub | sbb | cmp | test | and | or | xor
  deriving DecidableEq

def validBinary (operation : BinaryOp) (destination source : Operand) : Bool :=
  validMove destination source &&
    (match destination.width, source with
    | some .qword, .immediate value => -(2^31) ≤ value && value < 2^31
    | _, _ => true) &&
    (match operation, source with | .test, .memory _ _ => false | _, _ => true)

inductive Condition where
  | equal | notEqual | below | aboveOrEqual | belowOrEqual | above | sign
  | less | greaterOrEqual | lessOrEqual | greater
  deriving DecidableEq

def validConditionalMove (destination source : Operand) : Bool :=
  match destination with
  | .reg16 _ | .reg32 _ | .reg64 _ => source.width == destination.width
  | _ => false

def validImul (destination source : Operand) (immediate : Option Int) : Bool :=
  validConditionalMove destination source &&
    match immediate with
    | none => true
    | some value => validBinary .add destination (.immediate value)

inductive ShiftOp where
  | shl | shr
  deriving DecidableEq

def validShift (destination : Operand) (count : Nat) : Bool :=
  (match destination with | .reg8 _ => count % 32 < 8 | .reg32 _ | .reg64 _ => true | _ => false) && count < 256

def validLea (destination : Operand) : Bool :=
  match destination with
  | .reg16 _ | .reg32 _ | .reg64 _ => true
  | _ => false

inductive Op where
  | nop
  | movd (destination : Xmm) (source : Reg32)
  | pshufd (destination source : Xmm) (order : Nat)
  | loadXmm (operation : XmmMove) (destination : Xmm) (source : Address)
  | storeXmm (operation : XmmMove) (destination : Address) (source : Xmm)
  | binary (operation : BinaryOp) (destination source : Operand)
  | lea (destination : Operand) (source : Address)
  | movzx (destination : Reg32) (source : Operand)
  | movsxd (destination : Reg) (source : Operand)
  | mov (destination source : Operand)
  | shift (operation : ShiftOp) (destination : Operand) (count : Nat)
  | imul (destination source : Operand) (immediate : Option Int)
  | mul (source : Reg)
  | tzcnt (destination source : Operand)
  | not (destination : Operand)
  | inc (destination : Operand)
  | dec (destination : Operand)
  | jmp (target : BitVec 64)
  | jcc (condition : Condition) (target : BitVec 64)
  | setcc (condition : Condition) (destination : Operand)
  | cmovcc (condition : Condition) (destination source : Operand)
  | push (source : Reg)
  | pop (destination : Reg)
  | call (target : BitVec 64)
  | ret
  deriving DecidableEq
structure Instruction where
  address : BitVec 64
  length : Nat
  op : Op
  deriving DecidableEq
-- A search tree: `branch split left right` holds the instructions below `split` in `left` and the
-- rest in `right`, so a fetch scans one leaf however large the program. A small program is one leaf.
inductive Program where
  | leaf (instructions : List Instruction)
  | branch (split : BitVec 64) (left right : Program)
  deriving DecidableEq

def Program.fetch : Program → BitVec 64 → Option Instruction
  | .leaf instructions, address =>
    instructions.find? fun instruction => instruction.address == address &&
      0 < instruction.length && instruction.length ≤ 15
  | .branch split left right, address =>
    if address < split then left.fetch address else right.fetch address

end Rivet
