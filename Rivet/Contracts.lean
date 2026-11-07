module
public import Rivet.Model
import Rivet.ExecutionProperties
@[expose] public section
namespace Rivet

abbrev InstructionAt (program : Program) (address : Nat) (instruction : Op) : Prop :=
  (program.fetch address).map Instruction.op = some instruction

@[simp] theorem execute_zero (program : Program) (initial : MachineState) {choices : FlagChoices} :
    execute program 0 initial choices = initial := by rfl

theorem execute_execute (program : Program) (later earlier : Nat) (initial : MachineState)
    {choices : FlagChoices} :
    execute program later (execute program earlier initial choices) (choices.drop earlier) =
      execute program (earlier + later) initial choices := (execute_add program earlier later initial).symm

@[simp] theorem execute_fault (program : Program) (steps : Nat) (initial : MachineState)
    {choices : FlagChoices} (faulted : initial.status = .fault) :
    execute program steps initial choices = initial :=
  execute_stopped program steps initial (by simp [faulted, ExecutionStatus.isRunning])

theorem execute_reads_mono (program : Program) (steps : Nat) (initial : MachineState) (access : Access)
    {choices : FlagChoices} (recorded : access ∈ initial.readHistory) :
    access ∈ (execute program steps initial choices).readHistory :=
  execute_reads_monotone program initial steps access recorded

theorem execute_preserves_register (program : Program) (steps : Nat) (initial : MachineState)
    (register : Reg) {choices : FlagChoices}
    (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    (execute program steps initial choices).registers register = initial.registers register := by
  apply execute_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

/-- Some finite execution reaches the final state. This alone does not guarantee
termination or correctness for every choice of undefined flags. -/
def Reaches (program : Program) (initial final : MachineState) : Prop :=
  ∃ (choices : FlagChoices) (steps : Nat), execute program steps initial choices = final

theorem Reaches.refl : Reaches program state state := ⟨fun _ => ⟨false, false, false⟩, 0, rfl⟩

/-- Use a finite prefix of one supply, then continue with another. -/
private def appendChoices (choices : FlagChoices) (count : Nat) (rest : FlagChoices) : FlagChoices :=
  fun index => if index < count then choices index else rest (index - count)

@[simp] private theorem drop_appendChoices (choices rest : FlagChoices) (count : Nat) :
    (appendChoices choices count rest).drop count = rest := by
  funext index
  simp [FlagChoices.drop, appendChoices, Nat.not_lt_of_ge (Nat.le_add_right count index)]

/-- Bounded execution only depends on the corresponding finite prefix of choices. -/
private theorem execute_congr_choices (program : Program) (steps : Nat) (state : MachineState)
    (first second : FlagChoices) (agree : ∀ index < steps, first index = second index) :
    execute program steps state first = execute program steps state second := by
  induction steps generalizing state first second with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [execute, agree 0 (Nat.zero_lt_succ _)]
    apply inductionHypothesis
    intro index bound
    exact agree (1 + index) (by omega)

@[simp] private theorem execute_appendChoices (program : Program) (steps : Nat) (state : MachineState)
    (choices rest : FlagChoices) :
    execute program steps state (appendChoices choices steps rest) = execute program steps state choices := by
  apply execute_congr_choices
  intro index bound
  simp [appendChoices, bound]

theorem Reaches.trans (first : Reaches program initial intermediate)
    (second : Reaches program intermediate final) : Reaches program initial final := by
  obtain ⟨choices, earlier, rfl⟩ := first
  obtain ⟨rest, later, rfl⟩ := second
  exact ⟨appendChoices choices earlier rest, earlier + later, by simp [execute_add]⟩

/-- For every choice supply, a block eventually satisfies its postcondition.
The witness may depend on the supply; no instruction budget is required of callers. -/
structure Ensures (program : Program) (precondition postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ initial, precondition initial → ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute program steps initial choices = final) ∧ postcondition final

/-- Obtain one reachable result. The contract itself guarantees the postcondition
for every choice supply; this theorem does not expose that implementation detail. -/
theorem Ensures.run (contract : Ensures program precondition postcondition)
    (initial : MachineState) (assumption : precondition initial) :
    ∃ final, Reaches program initial final ∧ postcondition final := by
  let choices : FlagChoices := fun _ => ⟨false, false, false⟩
  obtain ⟨final, reached, result⟩ := contract.allChoices initial assumption choices
  exact ⟨final, ⟨choices, reached⟩, result⟩

/-- Prove a contract separately for each initial state satisfying the precondition. -/
theorem Ensures.intro
    (body : ∀ initial, precondition initial → Ensures program (· = initial) postcondition) :
    Ensures program precondition postcondition :=
  ⟨fun initial assumption => (body initial assumption).allChoices initial rfl⟩

/-- Establish a contract by one instruction, for every permitted undefined flag value.
Instruction rules use this when the model has no more specific rule yet. -/
theorem Ensures.of_step
    (transition : ∀ initial, precondition initial → ∀ undefinedFlags,
      postcondition (step program initial undefinedFlags)) :
    Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  exact ⟨step program initial (choices 0), ⟨1, rfl⟩, transition initial assumption (choices 0)⟩

/-- Retain reachability alongside a block's result, for deriving facts about the
initial/final state pair without opening the execution witness. -/
theorem Ensures.with_reachability (contract : Ensures program (· = initial) postcondition) :
    Ensures program (· = initial) (fun final => Reaches program initial final ∧ postcondition final) := by
  constructor
  intro actual equal choices
  subst actual
  obtain ⟨final, reached, result⟩ := contract.allChoices initial rfl choices
  exact ⟨final, reached, ⟨choices, reached⟩, result⟩

theorem Ensures.refl : Ensures program predicate predicate :=
  ⟨fun initial assumption _ => ⟨initial, ⟨0, rfl⟩, assumption⟩⟩

theorem Ensures.seq (first : Ensures program precondition intermediate)
    (second : Ensures program intermediate postcondition) : Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨middle, ⟨earlier, rfl⟩, holds⟩ := first.allChoices initial assumption choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := second.allChoices _ holds (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Ensures.consequence (contract : Ensures program precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures program strongerPrecondition weakerPostcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨final, reached, result⟩ := contract.allChoices initial (strengthenPrecondition _ assumption) choices
  exact ⟨final, reached, weakenPostcondition _ result⟩

/-- Iterate blocks while a natural-valued measure decreases. No instruction counts enter the rule. -/
theorem Ensures.loop (invariant finished : MachineState → Prop) (measure : MachineState → Nat)
    (body : ∀ initial, invariant initial → ¬ finished initial →
      Ensures program (· = initial) (fun final => invariant final ∧ measure final < measure initial)) :
    Ensures program invariant (fun final => invariant final ∧ finished final) := by
  constructor
  intro initial assumption choices
  induction bound : measure initial using Nat.strongRecOn generalizing initial choices with
  | ind bound inductionHypothesis =>
    by_cases done : finished initial
    · exact ⟨initial, ⟨0, rfl⟩, assumption, done⟩
    · obtain ⟨middle, ⟨earlier, rfl⟩, holds, decreases⟩ := (body initial assumption done).allChoices initial rfl choices
      obtain ⟨final, ⟨later, reached⟩, result⟩ := inductionHypothesis _ (by omega) _ holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

/-- A property holds at every finite reachable state, under every choice supply. -/
def Always (program : Program) (initial : MachineState) (property : MachineState → Prop) : Prop :=
  ∀ final, Reaches program initial final → property final

theorem Always.induction (initially : property initial)
    (preserved : ∀ state, property state → ∀ undefinedFlags, property (step program state undefinedFlags)) :
    Always program initial property := by
  intro final ⟨choices, steps, equal⟩
  subst final
  induction steps generalizing initial choices with
  | zero => exact initially
  | succ steps inductionHypothesis => exact inductionHypothesis (preserved initial initially (choices 0)) _

/-- Every finite prefix under every choice supply is still running. -/
def Diverges (program : Program) (initial : MachineState) : Prop :=
  Always program initial (fun state => state.status.isRunning = true)

theorem Reaches.stopped (reached : Reaches program initial final)
    (stopped : initial.status.isRunning = false) : final = initial := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_stopped _ _ _ stopped

theorem Reaches.not_fault (reached : Reaches program initial final)
    (notFaulted : final.status ≠ .fault) : initial.status ≠ .fault := by
  intro faulted
  have equal := reached.stopped (by simp [faulted, ExecutionStatus.isRunning])
  subst final
  exact notFaulted faulted

theorem Reaches.reads_mono (reached : Reaches program initial final)
    (recorded : access ∈ initial.readHistory) : access ∈ final.readHistory := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_reads_mono _ steps _ _ recorded

theorem Reaches.preserves_register (reached : Reaches program initial final) (register : Reg)
    (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    final.registers register = initial.registers register := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_preserves_register _ steps _ register unchanged

/-- Positive progress through running checkpoints, for every choice, proves divergence. -/
theorem Diverges.of_progress (invariant : MachineState → Prop) (initially : invariant initial)
    (progress : ∀ state, invariant state → state.status.isRunning = true ∧
      ∀ undefinedFlags, Ensures program (· = step program state undefinedFlags) invariant) :
    Diverges program initial := by
  intro final ⟨choices, steps, equal⟩
  subst final
  induction steps using Nat.strongRecOn generalizing initial choices with
  | ind steps inductionHypothesis =>
    obtain ⟨running, continuation⟩ := progress initial initially
    obtain ⟨nextState, ⟨remainingSteps, rfl⟩, nextInvariant⟩ := (continuation (choices 0)).allChoices _ rfl (choices.drop 1)
    let length := remainingSteps + 1
    have positive : 0 < length := Nat.zero_lt_succ _
    change invariant (execute program length initial choices) at nextInvariant
    by_cases order : length ≤ steps
    · have rest := inductionHypothesis (steps-length) (by omega) nextInvariant (choices.drop length)
      simpa [execute_execute, Nat.add_sub_of_le order] using rest
    · cases stoppedBool : (execute program steps initial choices).status.isRunning with
      | true => rfl
      | false =>
        have unchanged := execute_stopped program (length-steps) (execute program steps initial choices)
          (choices := choices.drop steps) stoppedBool
        rw [execute_execute, Nat.add_sub_of_le (by omega : steps ≤ length)] at unchanged
        have nextRunning := (progress _ nextInvariant).1
        rw [unchanged] at nextRunning
        simp [stoppedBool] at nextRunning

private theorem one (code : InstructionAt program address instruction)
    (location : initial.status = .running address) (undefinedFlags : FlagValues) :
    step program initial undefinedFlags = stepOp instruction (program.nextAddress address) initial undefinedFlags := by
  simp only [step, location]
  cases entry : program.fetch address with
  | none => simp [InstructionAt, entry] at code
  | some found => simp [InstructionAt, entry] at code; simp [code, Program.nextAddress, entry]

-- Every instruction has the same contract shape as a multi-instruction block.
-- `code` is checked automatically for concrete programs, or supplied explicitly.
theorem clear (program : Program) (address : Nat) (destination : Reg32) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .xor (.reg32 destination) (.reg32 destination)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination.parent 0 with
      status := .running (program.nextAddress address), zeroFlag := true, carryFlag := false, signFlag := false }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, Width.bits,
    Width.bytes, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance, MachineState.write]
  all_goals rfl

theorem test_zero (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .test (.reg64 register) (.reg64 register)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address), zeroFlag := initial.registers register == 0, carryFlag := false, signFlag := (initial.registers register).msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, Width.bits,
    Width.bytes, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance]
  all_goals rfl

theorem read_byte (program : Program) (address : Nat) (destination : Reg32) (base : Reg) (initial : MachineState)
    (location : initial.status = .running address) (allowed : initial.readable (initial.registers base).toNat = true)
    (code : InstructionAt program address (.movzx destination (.memory .byte (Address.baseOnly base))) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write destination.parent (BitVec.ofNat 64 (initial.memory (initial.registers base).toNat).val) with
      status := .running (program.nextAddress address), readHistory := initial.readHistory ++ [⟨(initial.registers base).toNat,1⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have bound : (initial.registers base).toNat + 1 ≤ word := by
    have := (initial.registers base).isLt
    unfold word
    omega
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next, Address.evaluate, Address.baseOnly, Scale.value,
    Operand.width, MachineState.canRead, permits, Width.bytes, MachineState.readOperand,
    readMemory, MachineState.recordRead] <;> try rfl

theorem add (program : Program) (address : Nat) (destination source : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .add (.reg64 destination) (.reg64 source)) := by decide +kernel) :
    let result := initial.registers destination + initial.registers source
    Ensures program (· = initial) (· = { initial.write destination result with
      status := .running (program.nextAddress address), zeroFlag := result == 0, carryFlag := result < initial.registers destination, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, Width.bits,
    Width.bytes, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance, MachineState.write]
  all_goals rfl

theorem inc (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.inc register) := by decide +kernel) :
    let result := initial.registers register + 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (program.nextAddress address), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem dec (program : Program) (address : Nat) (register : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.dec register) := by decide +kernel) :
    let result := initial.registers register - 1
    Ensures program (· = initial) (· = { initial.write register result with
      status := .running (program.nextAddress address), zeroFlag := result == 0, signFlag := result.msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, MachineState.write, stepOp, next] <;> try rfl

theorem branch_zero (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .equal target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then target else program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, stepOp, Condition.holds]
  split <;> rfl

theorem branch_nonzero (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .notEqual target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.zeroFlag then program.nextAddress address else target) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [ExecutionStatus.advance, stepOp, Condition.holds]
  cases initial.zeroFlag <;> rfl

theorem call (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (writable : permits initial.writable (initial.registers .rsp - 8).toNat 8 = true := by rfl)
    (code : InstructionAt program address (.call target) := by decide +kernel) :
    Ensures program (· = initial) (· = {
      (initial.writeMemory (initial.registers .rsp - 8).toNat .qword
        (BitVec.ofNat 64 (program.nextAddress address))).write .rsp (initial.registers .rsp - 8) with
      status := .running target }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp only [stepOp]
  rw [ite_eq_left writable]

theorem return_ (program : Program) (address : Nat) (initial : MachineState)
    (location : initial.status = .running address) (slot : initial.ValidReturnSlot)
    (code : InstructionAt program address .ret := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.write .rsp (initial.registers .rsp + 8) with
      status := .running initial.returnAddress, readHistory := initial.readHistory ++ [⟨(initial.registers .rsp).toNat,8⟩] }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp_all [MachineState.write, MachineState.ValidReturnSlot, MachineState.returnAddress, stepOp, read64]
theorem move (program : Program) (address : Nat) (destination source : Operand) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (valid : validMove destination source = true := by decide +kernel)
    (readable : initial.canRead source = true := by rfl)
    (writable : initial.canWrite destination = true := by rfl)
    (code : InstructionAt program address (.mov destination source) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.writeOperand destination (initial.readOperand source) with
      status := .running (program.nextAddress address), readHistory := (initial.recordRead source).readHistory }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, next, ExecutionStatus.advance, location, valid, readable, writable]

theorem compare (program : Program) (address : Nat) (left right : Reg) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.binary .cmp (.reg64 left) (.reg64 right)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with
      status := .running (program.nextAddress address)
      zeroFlag := initial.registers left == initial.registers right,
      carryFlag := initial.registers left < initial.registers right,
      signFlag := (initial.registers left - initial.registers right).msb }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  dsimp [stepOp, MachineState.binary, validBinary, validMove, Operand.width, Width.bits,
    Width.bytes, BinaryOp.writes, BinaryOp.result, BinaryOp.carry, MachineState.canRead,
    MachineState.canWrite, MachineState.readOperand, MachineState.writeOperand,
    MachineState.recordRead, next]
  simp_all [ExecutionStatus.advance]
  change (initial.registers left - initial.registers right == 0#64) =
    (initial.registers left == initial.registers right)
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem write_byte (program : Program) (address : Nat) (base : Reg) (source : Reg8) (initial : MachineState)
    (location : initial.status = .running address) (allowed : initial.writable (initial.registers base).toNat = true)
    (code : InstructionAt program address (.mov (.memory .byte (Address.baseOnly base)) (.reg8 source)) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial.storeByte (initial.registers base).toNat
      ⟨(initial.registers source.parent).toNat % 256, Nat.mod_lt _ (by decide)⟩ with
      status := .running (program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  have bound : (initial.registers base).toNat + 1 ≤ word := by
    have := (initial.registers base).isLt
    unfold word
    omega
  simp [stepOp, validMove, Operand.width, MachineState.canRead, MachineState.canWrite,
    MachineState.writeOperand, MachineState.readOperand, MachineState.recordRead,
    MachineState.writeMemory, Width.bytes, Address.evaluate, Address.baseOnly, Scale.value,
    permits, next, ExecutionStatus.advance, MachineState.storeByte, location, allowed, bound]

theorem branch_below (program : Program) (address target : Nat) (initial : MachineState)
    (location : initial.status = .running address := by rfl)
    (code : InstructionAt program address (.jcc .below target) := by decide +kernel) :
    Ensures program (· = initial) (· = { initial with status := .running (if initial.carryFlag then target else program.nextAddress address) }) := by
  apply Ensures.of_step
  intro actual equal undefinedFlags
  subst actual
  rw [one code location undefinedFlags]
  simp [stepOp, ExecutionStatus.advance, Condition.holds, location]
  split <;> rfl

end Rivet
