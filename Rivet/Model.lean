module
public import Rivet.Memory
@[expose] public section
namespace Rivet

inductive ExecutionStatus where
  | running (address : Nat)
  | fault
  deriving DecidableEq
structure MachineState where
  registers : Reg → BitVec 64
  xmmRegisters : Xmm → BitVec 128 := fun _ => 0
  signFlag : Bool := false
  zeroFlag : Bool
  carryFlag : Bool := false
  memory : Memory
  status : ExecutionStatus
  readHistory : List Access

/-- Candidate values for flags an instruction leaves undefined. Defined and preserved
flags must not use these values. This is execution input, not architectural state. -/
structure FlagValues where
  signFlag : Bool
  zeroFlag : Bool

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

def ExecutionStatus.isRunning : ExecutionStatus → Bool
  | .running _ => true
  | _ => false

def ExecutionStatus.advance (nextAddress : Nat) : ExecutionStatus → ExecutionStatus
  | .running _ => .running nextAddress
  | stopped => stopped

def next (nextAddress : Nat) (state : MachineState) : MachineState :=
  { state with status := state.status.advance nextAddress }
def Address.evaluate (address : Address) (registers : Reg → BitVec 64) : BitVec 64 :=
  (address.base.map registers).getD 0 +
    (address.index.map registers).getD 0 * BitVec.ofNat 64 address.scale.value +
    BitVec.ofInt 64 address.displacement

/-- Write a whole value after its complete range has passed permission checks. -/
def MachineState.writeMemory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : MachineState :=
  { state with memory := state.memory.storeBytes address width.bytes (fun offset =>
      ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩) }

def MachineState.readOperand (state : MachineState) : Operand → BitVec 64
  | .reg8 register => ((state.registers register.parent).setWidth 8).setWidth 64
  | .reg16 register => ((state.registers register.parent).setWidth 16).setWidth 64
  | .reg32 register => ((state.registers register.parent).setWidth 32).setWidth 64
  | .reg64 register => state.registers register
  | .memory width address => (readBytes state.memory (address.evaluate state.registers).toNat width.bytes).setWidth 64
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
  | .memory width address => permits state.memory.readable (address.evaluate state.registers).toNat width.bytes
  | _ => true

def MachineState.canWrite (state : MachineState) : Operand → Bool
  | .memory width address => permits state.memory.writable (address.evaluate state.registers).toNat width.bytes
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
def MachineState.binary (state : MachineState) (operation : BinaryOp) (destination source : Operand) (nextAddress : Nat) : MachineState :=
  if validBinary operation destination source && state.canRead destination && state.canRead source &&
      (!operation.writes || state.canWrite destination) then
    let width := destination.width.getD .qword
    let left := (state.readOperand destination).setWidth width.bits
    let right := (state.readOperand source).setWidth width.bits
    let result := operation.result left right state.carryFlag
    let updated := if operation.writes then state.writeOperand destination (result.setWidth 64) else state
    next nextAddress { updated with
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

def stepOp (operation : Op) (nextAddress : Nat) (state : MachineState) (undefinedFlags : FlagValues) : MachineState :=
  match operation with
  | .nop => next nextAddress state
  | .movd destination source =>
    let value := ((state.registers source.parent).setWidth 32).setWidth 128
    next nextAddress { state with xmmRegisters := fun register =>
      if register = destination then value else state.xmmRegisters register }
  | .pshufd destination source order =>
    if order < 256 then
      let original := (state.xmmRegisters source).toNat
      let value := BitVec.ofNat 128 ((List.range 4).foldr (fun lane result =>
        let selected := order / 4^lane % 4
        (original / 2^(32 * selected)) % 2^32 + 2^32 * result) 0)
      next nextAddress { state with xmmRegisters := fun register =>
        if register = destination then value else state.xmmRegisters register }
    else { state with status := .fault }
  | .loadXmm _ destination source =>
    let address := (source.evaluate state.registers).toNat
    if permits state.memory.readable address 16 then
      let value := readBytes state.memory address 16
      next nextAddress { state with
        xmmRegisters := fun register => if register = destination then value else state.xmmRegisters register
        readHistory := state.readHistory ++ [⟨address, 16⟩] }
    else { state with status := .fault }
  | .storeXmm _ destination source =>
    let address := (destination.evaluate state.registers).toNat
    if permits state.memory.writable address 16 then
      let value := state.xmmRegisters source
      next nextAddress { state with memory := state.memory.storeBytes address 16 (fun offset =>
        ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩) }
    else { state with status := .fault }
  | .binary operation destination source => state.binary operation destination source nextAddress
  | .shift operation destination count =>
    if validShift destination count then
      let width := (destination.width.getD .qword).bits
      -- For the supported widths, count masking is reduction modulo 32 or 64.
      let count := count % width
      let value := (state.readOperand destination).setWidth width
      let result : BitVec width := match operation with
        | .shl => BitVec.shiftLeft value count
        | .shr => BitVec.ushiftRight value count
      -- Even a zero-count r32 shift clears the upper half of its parent register.
      let updated := state.writeOperand destination (result.setWidth 64)
      if count == 0 then next nextAddress updated else
        next nextAddress { updated with
          carryFlag := value.getLsbD (match operation with | .shl => width - count | .shr => count - 1)
          zeroFlag := result.toNat == 0
          signFlag := result.msb }
    else { state with status := .fault }
  | .imul destination source immediate =>
    if validImul destination source immediate && state.canRead source then
      let width := (destination.width.getD .qword).bits
      let sourceValue := (state.readOperand source).setWidth width
      let multiplier := match immediate with
        | none => (state.readOperand destination).setWidth width
        | some value => BitVec.ofInt width value
      let product := sourceValue.toInt * multiplier.toInt
      let result := BitVec.ofInt width product
      next nextAddress { state.writeOperand destination (result.setWidth 64) with
        carryFlag := result.toInt != product
        signFlag := undefinedFlags.signFlag
        zeroFlag := undefinedFlags.zeroFlag
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .lea destination address => next nextAddress (state.write destination (address.evaluate state.registers))
  | .movzx destination source =>
    if (source.width == some .byte || source.width == some .word) && state.canRead source then
      next nextAddress { state.write destination.parent (state.readOperand source) with
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .movsxd destination source =>
    if source.width == some .dword && state.canRead source then
      next nextAddress { state.write destination ((state.readOperand source).setWidth 32 |>.signExtend 64) with
        readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .mov destination source =>
    if validMove destination source && state.canRead source && state.canWrite destination then
      -- Read and address calculation use the pre-instruction registers, including aliases.
      let result := state.writeOperand destination (state.readOperand source)
      next nextAddress { result with readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .not destination =>
    if state.canRead destination && state.canWrite destination then
      next nextAddress { state.writeOperand destination (~~~(state.readOperand destination)) with
        readHistory := (state.recordRead destination).readHistory }
    else { state with status := .fault }
  | .inc destination =>
    let result := state.registers destination + 1
    next nextAddress { state.write destination result with zeroFlag := result == 0, signFlag := result.msb }
  | .dec destination =>
    let result := state.registers destination - 1
    next nextAddress { state.write destination result with zeroFlag := result == 0, signFlag := result.msb }
  | .jmp target => { state with status := .running target }
  | .jcc condition target =>
    { state with status := if condition.holds state then .running target else state.status.advance nextAddress }
  | .setcc condition destination =>
    if destination.width == some .byte && state.canWrite destination then
      next nextAddress (state.writeOperand destination (if condition.holds state then 1 else 0))
    else { state with status := .fault }
  | .cmovcc condition destination source =>
    -- Memory sources are read even when the condition is false. Writing the old
    -- destination through its operand also clears the upper half of r32.
    if validConditionalMove destination source && state.canRead source then
      let value := if condition.holds state then state.readOperand source else state.readOperand destination
      next nextAddress { state.writeOperand destination value with readHistory := (state.recordRead source).readHistory }
    else { state with status := .fault }
  | .push source =>
    let pointer := state.registers .rsp - 8
    if permits state.memory.writable pointer.toNat 8 then
      -- PUSH RSP stores the original pointer, before decrementing it.
      next nextAddress ((state.writeMemory pointer.toNat .qword (state.registers source)).write .rsp pointer)
    else { state with status := .fault }
  | .pop destination =>
    let address := (state.registers .rsp).toNat
    if permits state.memory.readable address 8 then
      -- Write the destination last: POP RSP replaces the incremented pointer.
      let result := (state.write .rsp (state.registers .rsp + 8)).write destination
        (readBytes state.memory address 8)
      next nextAddress { result with readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }
  | .call target =>
    let pointer := state.registers .rsp - 8
    if permits state.memory.writable pointer.toNat 8 then
      { (state.writeMemory pointer.toNat .qword (BitVec.ofNat 64 nextAddress)).write .rsp pointer with
        status := .running target }
    else { state with status := .fault }
  | .ret =>
    let address := (state.registers .rsp).toNat
    if address + 8 ≤ word && (List.range 8).all (fun offset => state.memory.readable (address+offset)) then
      { state.write .rsp (state.registers .rsp + 8) with
        status := .running ((readBytes state.memory address 8).toNat)
        readHistory := state.readHistory ++ [⟨address,8⟩] }
    else { state with status := .fault }

def step (program : Program) (state : MachineState) (undefinedFlags : FlagValues) : MachineState :=
  match state.status with
  | .running address => match program.fetch address with
    | some instruction => stepOp instruction.op ((address + instruction.length) % word) state undefinedFlags
    | none => { state with status := .fault }
  | _ => state

def execute (program : Program) (steps : Nat) (state : MachineState) (choices : FlagChoices) : MachineState :=
  match steps with
  | 0 => state
  | remainingSteps+1 => execute program remainingSteps (step program state (choices 0)) (choices.drop 1)

/-- The little-endian address stored in the current stack return slot. -/
def MachineState.returnAddress (state : MachineState) : Nat :=
  (readBytes state.memory (state.registers .rsp).toNat 8).toNat

def MachineState.ValidReturnSlot (state : MachineState) : Prop :=
  (state.registers .rsp).toNat + 8 ≤ word ∧
    (List.range 8).all (fun offset => state.memory.readable ((state.registers .rsp).toNat + offset)) = true

def AtInstruction (state : MachineState) (address : Nat) : Prop :=
  state.status = .running address

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
