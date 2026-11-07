module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

inductive ExecutionStatus where
  | running (instructionIndex : Nat)
  | returned (address : Nat)
  | fault
  deriving DecidableEq, Repr
structure MachineState where
  registers : Reg → BitVec 64
  signFlag : Bool := false
  zeroFlag : Bool
  carryFlag : Bool := false
  memory : Nat → Fin 256
  readable : Nat → Bool
  writable : Nat → Bool := fun _ => false
  status : ExecutionStatus
  readHistory : List Access

/-- Candidate values for flags an instruction leaves undefined. Defined and preserved
flags must not use these values. This is execution input, not architectural state. -/
structure FlagValues where
  signFlag : Bool
  zeroFlag : Bool
  carryFlag : Bool
  deriving Repr

/-- One set of candidate bits per execution step, including repeated loop iterations. -/
abbrev FlagChoices := Nat → FlagValues

def FlagChoices.drop (choices : FlagChoices) (count : Nat) : FlagChoices :=
  fun index => choices (count + index)

@[simp] private theorem FlagChoices.drop_zero (choices : FlagChoices) : choices.drop 0 = choices := by
  funext index
  simp [drop]

@[simp] private theorem FlagChoices.drop_drop (choices : FlagChoices) (first second : Nat) :
    (choices.drop first).drop second = choices.drop (first + second) := by
  funext index
  simp [drop, Nat.add_assoc]

/-- Update one register; its width is enforced by the value's type. -/
def MachineState.write (state : MachineState) (register : Reg) (value : BitVec 64) : MachineState :=
  { state with registers := fun otherRegister =>
      if otherRegister = register then value else state.registers otherRegister }

/-- Update one byte; permission checks belong to the instruction semantics. -/
def MachineState.storeByte (state : MachineState) (address : Nat) (value : Fin 256) : MachineState :=
  { state with memory := fun otherAddress => if otherAddress = address then value else state.memory otherAddress }

def ExecutionStatus.isRunning : ExecutionStatus → Bool
  | .running _ => true
  | _ => false

def ExecutionStatus.advance : ExecutionStatus → ExecutionStatus
  | .running index => .running (index + 1)
  | stopped => stopped

def next (state : MachineState) : MachineState := { state with status := state.status.advance }
def read64 (memory : Nat → Fin 256) (address : Nat) : Nat :=
  (List.range 8).foldr (fun offset value => (memory (address+offset)).val + 256*value) 0

def Address.evaluate (address : Address) (registers : Reg → BitVec 64) : BitVec 64 :=
  (address.base.map registers).getD 0 +
    (address.index.map registers).getD 0 * BitVec.ofNat 64 address.scale.value +
    BitVec.ofInt 64 address.displacement

/-- Multi-byte accesses must fit the address space and have permission for every byte. -/
def permits (permission : Nat → Bool) (address size : Nat) : Bool :=
  address + size ≤ word && (List.range size).all (fun offset => permission (address + offset))

def readMemory (memory : Nat → Fin 256) (address : Nat) (width : Width) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range width.bytes).foldr
    (fun offset value => (memory (address + offset)).val + 256 * value) 0)

/-- Write a whole value after its complete range has passed permission checks. -/
def MachineState.writeMemory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : MachineState :=
  (List.range width.bytes).foldl (fun current offset =>
    current.storeByte (address + offset)
      ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩) state

def MachineState.readOperand (state : MachineState) : Operand → BitVec 64
  | .reg8 register => ((state.registers register.parent).setWidth 8).setWidth 64
  | .reg16 register => ((state.registers register.parent).setWidth 16).setWidth 64
  | .reg32 register => ((state.registers register.parent).setWidth 32).setWidth 64
  | .reg64 register => state.registers register
  | .memory width address => readMemory state.memory (address.evaluate state.registers).toNat width
  | .immediate value => BitVec.ofInt 64 value

def MachineState.writeOperand (state : MachineState) (operand : Operand) (value : BitVec 64) : MachineState :=
  match operand with
  | .reg8 register => state.write register.parent
      ((state.registers register.parent &&& ~~~(255#64)) ||| ((value.setWidth 8).setWidth 64))
  | .reg16 register => state.write register.parent
      ((state.registers register.parent &&& ~~~(65535#64)) ||| ((value.setWidth 16).setWidth 64))
  | .reg32 register => state.write register.parent ((value.setWidth 32).setWidth 64)
  | .reg64 register => state.write register value
  | .memory width address => state.writeMemory (address.evaluate state.registers).toNat width value
  | .immediate _ => state

def MachineState.canRead (state : MachineState) : Operand → Bool
  | .memory width address => permits state.readable (address.evaluate state.registers).toNat width.bytes
  | _ => true

def MachineState.canWrite (state : MachineState) : Operand → Bool
  | .memory width address => permits state.writable (address.evaluate state.registers).toNat width.bytes
  | .immediate _ => false
  | _ => true

def MachineState.recordRead (state : MachineState) : Operand → MachineState
  | .memory width address => { state with readHistory := state.readHistory ++
      [⟨(address.evaluate state.registers).toNat, width.bytes⟩] }
  | _ => state

def BinaryOp.result (operation : BinaryOp) (left right : BitVec width) (carryIn : Bool) : BitVec width :=
  match operation with
  | .add => left + right
  | .sub | .cmp => left - right
  | .sbb => left - right - (if carryIn then 1 else 0)
  | .and | .test => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

def BinaryOp.carry (operation : BinaryOp) (left right result : BitVec width) (carryIn : Bool) : Bool :=
  match operation with
  | .add => result < left
  | .sub | .cmp => left < right
  | .sbb => left < right || (carryIn && left == right)
  | _ => false

/-- Read both operands from the initial state; commit flags, memory, and history only on success. -/
def MachineState.binary (state : MachineState) (operation : BinaryOp) (destination source : Operand) : MachineState :=
  if validBinary operation destination source && state.canRead destination && state.canRead source &&
      (!operation.writes || state.canWrite destination) then
    let width := destination.width.getD .qword
    let left := (state.readOperand destination).setWidth width.bits
    let right := (state.readOperand source).setWidth width.bits
    let result := operation.result left right state.carryFlag
    let updated := if operation.writes then state.writeOperand destination (result.setWidth 64) else state
    next { updated with
      zeroFlag := result == 0
      signFlag := result.msb
      carryFlag := operation.carry left right result state.carryFlag,
      readHistory := ((state.recordRead destination).recordRead source).readHistory }
  else { state with status := .fault }

def Condition.holds (condition : Condition) (state : MachineState) : Bool :=
  match condition with
  | .equal => state.zeroFlag
  | .notEqual => !state.zeroFlag
  | .below => state.carryFlag
  | .aboveOrEqual => !state.carryFlag
  | .belowOrEqual => state.carryFlag || state.zeroFlag
  | .above => !state.carryFlag && !state.zeroFlag
  | .sign => state.signFlag

def stepOp (operation : Op) (state : MachineState) (undefinedFlags : FlagValues) : MachineState :=
  match operation with
  | .binary operation destination source => state.binary operation destination source
  | .imul destination source immediate =>
    if validImul destination source immediate && state.canRead source then
      let width := (destination.width.getD .qword).bits
      let sourceValue := (state.readOperand source).setWidth width
      let multiplier := match immediate with
        | none => (state.readOperand destination).setWidth width
        | some value => BitVec.ofInt width value
      let product := sourceValue.toInt * multiplier.toInt
      let result := BitVec.ofInt width product
      next { state.writeOperand destination (result.setWidth 64) with
        carryFlag := result.toInt != product
        signFlag := undefinedFlags.signFlag
        zeroFlag := undefinedFlags.zeroFlag
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .lea destination address => next (state.write destination (address.evaluate state.registers))
  | .movzx destination source =>
    if (source.width == some .byte || source.width == some .word) && state.canRead source then
      next { state.write destination.parent (state.readOperand source) with
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .movsxd destination source =>
    if source.width == some .dword && state.canRead source then
      next { state.write destination ((state.readOperand source).setWidth 32 |>.signExtend 64) with
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .mov destination source =>
    if validMove destination source && state.canRead source && state.canWrite destination then
      -- Read and address calculation use the pre-instruction registers, including aliases.
      let result := state.writeOperand destination (state.readOperand source)
      next { result with readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .not destination =>
    if state.canRead destination && state.canWrite destination then
      next { state.writeOperand destination (~~~(state.readOperand destination)) with
        readHistory := (state.recordRead destination).readHistory }
    else { state with status := .fault }
  | .inc destination =>
    let result := state.registers destination + 1
    next { state.write destination result with zeroFlag := result == 0, signFlag := result.msb }
  | .dec destination =>
    let result := state.registers destination - 1
    next { state.write destination result with zeroFlag := result == 0, signFlag := result.msb }
  | .jmp target => { state with status := .running target }
  | .jcc condition target =>
    { state with status := if condition.holds state then .running target else state.status.advance }
  | .setcc condition destination =>
    if destination.width == some .byte && state.canWrite destination then
      next (state.writeOperand destination (if condition.holds state then 1 else 0))
    else { state with status := .fault }
  | .cmovcc condition destination source =>
    -- Memory sources are read even when the condition is false. Writing the old
    -- destination through its operand also clears the upper half of r32.
    if validConditionalMove destination source && state.canRead source then
      let value := if condition.holds state then state.readOperand source else state.readOperand destination
      next { state.writeOperand destination value with readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .push source =>
    let pointer := state.registers .rsp - 8
    if permits state.writable pointer.toNat 8 then
      -- PUSH RSP stores the original pointer, before decrementing it.
      next ((state.writeMemory pointer.toNat .qword (state.registers source)).write .rsp pointer)
    else { state with status := .fault }
  | .pop destination =>
    let address := (state.registers .rsp).toNat
    if permits state.readable address 8 then
      -- Write the destination last: POP RSP replaces the incremented pointer.
      let result := (state.write .rsp (state.registers .rsp + 8)).write destination
        (readMemory state.memory address .qword)
      next { result with readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }
  | .ret =>
    let address := (state.registers .rsp).toNat
    if address + 8 ≤ word && (List.range 8).all (fun offset => state.readable (address+offset)) then
      { state.write .rsp (state.registers .rsp + 8) with
        status := .returned (read64 state.memory address)
        readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }

def step (program : Program) (state : MachineState) (undefinedFlags : FlagValues) : MachineState :=
  match state.status with
  | .running index => match program[index]? with
    | some instruction => stepOp instruction.op state undefinedFlags
    | none => { state with status := .fault }
  | _ => state

def execute (program : Program) (steps : Nat) (state : MachineState) (choices : FlagChoices) : MachineState :=
  match steps with
  | 0 => state
  | remainingSteps+1 => execute program remainingSteps (step program state (choices 0)) (choices.drop 1)

/-- The little-endian address stored in the current stack return slot. -/
def MachineState.returnAddress (state : MachineState) : Nat :=
  read64 state.memory (state.registers .rsp).toNat

def MachineState.ValidReturnSlot (state : MachineState) : Prop :=
  (state.registers .rsp).toNat + 8 ≤ word ∧
    (List.range 8).all (fun offset => state.readable ((state.registers .rsp).toNat + offset)) = true

def AtInstruction (state : MachineState) (index : Nat) : Prop :=
  state.status = .running index

theorem execute_add (program : Program) (firstSteps secondSteps : Nat) (state : MachineState)
    {choices : FlagChoices} :
    execute program (firstSteps + secondSteps) state choices =
      execute program secondSteps (execute program firstSteps state choices) (choices.drop firstSteps) := by
  induction firstSteps generalizing state choices with
  | zero => simp [execute]
  | succ firstSteps inductionHypothesis =>
    simpa [Nat.succ_add, execute, Nat.add_comm] using
      inductionHypothesis (step program state (choices 0)) (choices := choices.drop 1)

end Rivet
