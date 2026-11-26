module
public import Rivet.Interpreter.Syntax

@[expose] public section
namespace Rivet

abbrev Code := BitVec 64 → Option (Fin 256)

def Code.ofBytes (base : BitVec 64) (bytes : List (Fin 256)) : Code := fun address =>
  if base.toNat ≤ address.toNat then bytes[address.toNat - base.toNat]? else none

structure DecodePrefixes where
  word : Bool := false
  rep : Bool := false
  segment : Bool := false
  addr32 : Bool := false
  rex : Nat := 0

mutual
  inductive DecodeState where
    | opcode (p : DecodePrefixes)
    | byte (next : Fin 256 → DecodeReply)
  inductive DecodeReply where
    | more (front : DecodeState)
    | done (finish : BitVec 64 → Op)
    | reject
end

namespace Decode
abbrev Reply := DecodeReply
abbrev Rip := BitVec 64

def byte (next : Nat → Reply) : Reply :=
  .more (.byte fun b => next b.val)

def littleEndian (count : Nat) (next : Nat → Reply) : Reply :=
  let rec read : Nat → Nat → Nat → Reply
    | 0, _, value => next value
    | n+1, shift, value => byte fun b => read n (shift + 8) (value + (b <<< shift))
  read count 0 0

def signed (size value : Nat) : Int := (BitVec.ofNat (8 * size) value).toInt

def imm (size : Nat) (extend : Bool) (next : Int → Reply) : Reply :=
  littleEndian size fun n => next (if extend then signed size n else Int.ofNat n)

def operandWidth (p : DecodePrefixes) : Width :=
  if p.rex.testBit 3 then .qword else if p.word then .word else .dword

def gpr : Nat → Reg
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx
  | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _ => .r15

def gpr32 : Nat → Reg32
  | 0 => .eax | 1 => .ecx | 2 => .edx | 3 => .ebx
  | 4 => .esp | 5 => .ebp | 6 => .esi | 7 => .edi
  | 8 => .r8d | 9 => .r9d | 10 => .r10d | 11 => .r11d
  | 12 => .r12d | 13 => .r13d | 14 => .r14d | _ => .r15d

def gpr16 : Nat → Reg16
  | 0 => .ax | 1 => .cx | 2 => .dx | 3 => .bx
  | 4 => .sp | 5 => .bp | 6 => .si | 7 => .di
  | 8 => .r8w | 9 => .r9w | 10 => .r10w | 11 => .r11w
  | 12 => .r12w | 13 => .r13w | 14 => .r14w | _ => .r15w

def gpr8 : Nat → Reg8
  | 0 => .al | 1 => .cl | 2 => .dl | 3 => .bl
  | 4 => .spl | 5 => .bpl | 6 => .sil | 7 => .dil
  | 8 => .r8l | 9 => .r9l | 10 => .r10l | 11 => .r11l
  | 12 => .r12l | 13 => .r13l | 14 => .r14l | _ => .r15l

def xmm : Nat → Xmm
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

def register (p : DecodePrefixes) (width : Width) (n : Nat) : Option Operand :=
  match width with
  | .byte => if p.rex == 0 && n ≥ 4 then none else some (.reg8 (gpr8 n))
  | .word => some (.reg16 (gpr16 n))
  | .dword => some (.reg32 (gpr32 n))
  | .qword => some (.reg64 (gpr n))

inductive RM where
  | reg (n : Nat)
  | mem (resolve : Rip → Address)

def scalar (p : DecodePrefixes) (width : Width) (rm : RM)
    (next : (Rip → Operand) → Reply) : Reply :=
  match rm with
  | .mem addr => next fun rip => .memory width (addr rip)
  | .reg n => match register p width n with
    | some r => next fun _ => r
    | none => .reject

def displacement (mode : Nat) (addr : Address) (baseAbsent : Bool)
    (next : RM → Reply) : Reply :=
  let size := if mode == 1 then 1 else if mode == 2 || baseAbsent then 4 else 0
  imm size true fun d => next (.mem fun _ => { addr with displacement := d })

def modRM (p : DecodePrefixes) (next : Nat → RM → Reply) : Reply :=
  byte fun m =>
    let mode := m / 64
    let r := m / 8 % 8 + (p.rex / 4 % 2) * 8
    let low := m % 8
    let b := (p.rex % 2) * 8
    if mode == 3 then next r (.reg (low + b))
    else if low == 4 then byte fun sib =>
      let scale := match sib / 64 with | 0 => Scale.one | 1 => .two | 2 => .four | _ => .eight
      let i := sib / 8 % 8 + (p.rex / 2 % 2) * 8
      let index := if i == 4 then none else some (gpr i)
      let absent := mode == 0 && sib % 8 == 5
      let base := if absent then none else some (gpr (sib % 8 + b))
      displacement mode { base, index, scale } absent (next r)
    else if mode == 0 && low == 5 then
      imm 4 true fun d => next r (.mem fun rip => { displacement := (rip + BitVec.ofInt 64 d).toInt })
    else displacement mode { base := some (gpr (low + b)) } false (next r)

def pair (p : DecodePrefixes) (width : Width) (reverse : Bool)
    (op : Operand → Operand → Op) : Reply :=
  modRM p fun r rm => match register p width r with
    | none => .reject
    | some reg => scalar p width rm fun resolve => .done fun rip =>
      if reverse then op reg (resolve rip) else op (resolve rip) reg

def group : Nat → Option BinaryOp
  | 0 => some .add | 1 => some .or | 3 => some .sbb | 4 => some .and
  | 5 => some .sub | 6 => some .xor | 7 => some .cmp | _ => none

def condition : Nat → Option Condition
  | 2 => some .below | 3 => some .aboveOrEqual | 4 => some .equal | 5 => some .notEqual
  | 6 => some .belowOrEqual | 7 => some .above | 8 => some .sign
  | 12 => some .less | 13 => some .greaterOrEqual | 14 => some .lessOrEqual
  | 15 => some .greater | _ => none

def branch (size : Nat) (op : Rip → Op) : Reply :=
  imm size true fun d => .done fun rip => op (rip + BitVec.ofInt 64 d)

def ordinaryImm (width : Width) (next : Int → Reply) : Reply :=
  imm (min 4 width.bytes) (width == .qword) next

def extended (p : DecodePrefixes) (b : Nat) : Reply := Id.run do
  let width := operandWidth p
  if b == 0x1f && !p.rep then return modRM p fun ext _ =>
    if ext % 8 == 0 then .done fun _ => .nop else .reject
  if p.segment || p.addr32 then return .reject
  if p.rep && b == 0xbc then return pair p width true .tzcnt
  if b == 0x10 || b == 0x11 || b == 0x6f || b == 0x7f then
    let dqu := b == 0x6f || b == 0x7f
    if p.rep != dqu || p.word then return .reject
    let kind := if dqu then XmmMove.movdqu else .movups
    return modRM p fun r rm => match rm with
      | .mem addr => .done fun rip =>
        if b == 0x10 || b == 0x6f then .loadXmm kind (xmm r) (addr rip)
        else .storeXmm kind (addr rip) (xmm r)
      | _ => .reject
  if p.rep then return .reject
  if b == 0x05 then return if p.word then .reject else .done fun _ => .syscall
  if b == 0xaf then return pair p width true fun d s => .imul d s none
  if b == 0xb6 || b == 0xb7 then
    if width != .dword then return .reject
    return modRM p fun r rm => scalar p (if b == 0xb6 then .byte else .word) rm fun s =>
      .done fun rip => .movzx (gpr32 r) (s rip)
  if p.word && b == 0x6e && !p.rex.testBit 3 then
    return modRM p fun r rm => match rm with
      | .reg s => .done fun _ => .movd (xmm r) (gpr32 s)
      | _ => .reject
  if p.word && b == 0x70 then
    return modRM p fun r rm => match rm with
      | .reg s => byte fun order => .done fun _ => .pshufd (xmm r) (xmm s) order
      | _ => .reject
  let some cc := condition (b % 16) | return .reject
  match b / 16 with
  | 4 => return pair p width true (.cmovcc cc)
  | 8 => return if width == .word then .reject else branch 4 (.jcc cc)
  | 9 => return modRM p fun _ rm => scalar p .byte rm fun d => .done fun rip => .setcc cc (d rip)
  | _ => return .reject

def grouped (p : DecodePrefixes) (b : Nat) : Reply :=
  let w := if b % 2 == 0 then Width.byte else operandWidth p
  modRM p fun field rm => Id.run do
    -- REX.R extends registers, but never an opcode extension.
    let ext := field % 8
    if b == 0x8f || (b == 0xff && ext == 6) then
      if (b == 0x8f && ext != 0) || operandWidth p == .word then return .reject
      let .reg n := rm | return .reject
      return .done fun _ => if b == 0x8f then .pop (gpr n) else .push (gpr n)
    if b == 0xf7 && ext == 4 && w == .qword then
      let .reg n := rm | return .reject
      return .done fun _ => .mul (gpr n)
    if b == 0xc0 || b == 0xc1 || b == 0xd0 || b == 0xd1 then
      let .reg n := rm | return .reject
      let some d := register p w n | return .reject
      if ext != 4 && ext != 5 then return .reject
      let shift := if ext == 5 then ShiftOp.shr else .shl
      let finish := fun count => if validShift d count then DecodeReply.done fun _ => .shift shift d count
                                 else .reject
      return if b ≥ 0xd0 then finish 1 else byte finish
    return scalar p w rm fun d => Id.run do
      match b with
      | 0x80 | 0x81 | 0x83 =>
        let some op := group ext | return .reject
        let next := fun i => DecodeReply.done fun rip => .binary op (d rip) (.immediate i)
        return if b == 0x83 then imm 1 true next else ordinaryImm w next
      | 0xc6 | 0xc7 =>
        if ext != 0 then return .reject
        return ordinaryImm w fun i => .done fun rip => .mov (d rip) (.immediate i)
      | 0xf6 | 0xf7 =>
        if ext == 2 then return .done fun rip => .not (d rip)
        if ext > 1 then return .reject
        return ordinaryImm w fun i => .done fun rip => .binary .test (d rip) (.immediate i)
      | 0xfe | 0xff =>
        if ext > 1 then return .reject
        return .done fun rip => if ext == 0 then .inc (d rip) else .dec (d rip)
      | _ => return .reject

def opcode (p : DecodePrefixes) (b : Nat) : Reply := Id.run do
  if b == 0x0f then return byte (extended p)
  if b == 0x90 && p.rex % 2 == 0 && !p.rep then return .done fun _ => .nop
  if p.rep || p.segment || p.addr32 then return .reject
  let width := operandWidth p
  let w := if b % 2 == 0 then Width.byte else width
  if b < 0x40 then
    let some op := group (b / 8) | return .reject
    if b % 8 < 4 then return pair p w (b % 8 ≥ 2) (.binary op)
    if b % 8 ≥ 6 then return .reject
    let some acc := register p w 0 | return .reject
    return ordinaryImm w fun i => .done fun _ => .binary op acc (.immediate i)
  if b ≥ 0x50 && b < 0x60 then
    if width == .word then return .reject
    let r := gpr (b % 8 + p.rex % 2 * 8)
    return .done fun _ => if b < 0x58 then .push r else .pop r
  if b / 16 == 7 then
    if width == .word then return .reject
    let some cc := condition (b % 16) | return .reject
    return branch 1 (.jcc cc)
  if b / 16 == 11 then
    let size := if b < 0xb8 then Width.byte else width
    let some d := register p size (b % 8 + p.rex % 2 * 8) | return .reject
    return imm size.bytes false fun i => .done fun _ => .mov d (.immediate i)
  match b with
  | 0x63 =>
    if width != .qword then return .reject
    return modRM p fun r rm => scalar p .dword rm fun s => .done fun rip => .movsxd (gpr r) (s rip)
  | 0x69 | 0x6b =>
    return modRM p fun r rm => match register p width r with
      | none => .reject
      | some d => scalar p width rm fun s =>
        let next := fun i => DecodeReply.done fun rip => .imul d (s rip) (some i)
        if b == 0x6b then imm 1 true next else ordinaryImm width next
  | 0x84 | 0x85 => return pair p w false (.binary .test)
  | 0x88 | 0x89 | 0x8a | 0x8b => return pair p w (b ≥ 0x8a) .mov
  | 0x8d =>
    return modRM p fun r rm => match register p width r, rm with
      | some d, .mem addr => .done fun rip => .lea d (addr rip)
      | _, _ => .reject
  | 0xa0 | 0xa1 | 0xa2 | 0xa3 =>
    let some acc := register p w 0 | return .reject
    return imm 8 true fun d => .done fun _ =>
      let mem := Operand.memory w { displacement := d }
      if b < 0xa2 then .mov acc mem else .mov mem acc
  | 0xa8 | 0xa9 =>
    let some acc := register p w 0 | return .reject
    return ordinaryImm w fun i => .done fun _ => .binary .test acc (.immediate i)
  | 0xc3 => return if width == .word then .reject else .done fun _ => .ret
  | 0xe8 => return if width == .word then .reject else branch 4 .call
  | 0xe9 => return if width == .word then .reject else branch 4 .jmp
  | 0xeb => return if width == .word then .reject else branch 1 .jmp
  | 0x80 | 0x81 | 0x83 | 0x8f | 0xc0 | 0xc1 | 0xc6 | 0xc7
  | 0xd0 | 0xd1 | 0xf6 | 0xf7 | 0xfe | 0xff => return grouped p b
  | _ => return .reject

def scan (p : DecodePrefixes) (b : Nat) : Reply :=
  match b with
  | 0x66 => if p.word || p.rex != 0 then .reject else .more (.opcode { p with word := true })
  | 0xf3 => if p.rep || p.rex != 0 then .reject else .more (.opcode { p with rep := true })
  | 0x26 | 0x2e | 0x36 | 0x3e | 0x64 | 0x65 =>
    if p.segment || p.rex != 0 then .reject else .more (.opcode { p with segment := true })
  | 0x67 => if p.addr32 || p.rex != 0 then .reject else .more (.opcode { p with addr32 := true })
  | _ =>
    if 0x40 ≤ b && b < 0x50 then
      if p.rex != 0 then .reject else .more (.opcode { p with rex := b })
    else opcode p b
end Decode

def feed : DecodeState → Fin 256 → DecodeReply
  | .opcode p, b => Decode.scan p b.val
  | .byte next, b => next b

def Code.fetch (code : Code) (address : BitVec 64) : Option (Nat × Op) :=
  let rec read : Nat → Nat → DecodeState → Option (Nat × Op)
    | 0, _, _ => none
    | fuel+1, offset, state => do
      let b ← code (address + BitVec.ofNat 64 offset)
      match feed state b with
      | .reject => none
      | .done finish => some (offset + 1, finish (address + BitVec.ofNat 64 (offset + 1)))
      | .more next => read fuel (offset + 1) next
  read 15 0 (.opcode {})

end Rivet
