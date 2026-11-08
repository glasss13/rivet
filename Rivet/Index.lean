module
public import Rivet.Syntax
public meta import Lean
@[expose] public section
namespace Rivet

/-- Whether `Program.fetch` can return this instruction at its own address:
a 64-bit address and an x86 instruction length from 1 to 15. -/
def Instruction.fetchable (instruction : Instruction) : Bool :=
  instruction.address < word && 0 < instruction.length && instruction.length ≤ 15

/-- A binary search tree of instructions keyed by address. Lookup takes time
logarithmic in the program size for a balanced tree, including in the kernel. -/
inductive InstructionTree where
  | leaf
  | node (left : InstructionTree) (entry : Instruction) (right : InstructionTree)

namespace InstructionTree

def lookup : InstructionTree → Nat → Option Instruction
  | leaf, _ => none
  | node left entry right, address =>
    if address < entry.address then left.lookup address
    else if entry.address < address then right.lookup address
    else some entry

/-- Entries in order. -/
def toList : InstructionTree → List Instruction
  | leaf => []
  | node left entry right => left.toList ++ entry :: right.toList

end InstructionTree

/-- Strictly increasing addresses, checked by evaluation. -/
def increasingAddresses : List Instruction → Bool
  | first :: second :: rest => first.address < second.address && increasingAddresses (second :: rest)
  | _ => true

/-- `tree` holds exactly the fetchable instructions of `program`, in increasing
address order. Both fields are checked by evaluation (`rfl`) for a concrete program. -/
structure InstructionTree.Indexes (tree : InstructionTree) (program : Program) : Prop where
  entries : tree.toList = program.filter Instruction.fetchable
  increasing : increasingAddresses tree.toList = true

namespace InstructionTree

private theorem find?_fetch (program : List Instruction) (address : Nat) :
    program.find? (fun instruction => instruction.address == address && address < word &&
      0 < instruction.length && instruction.length ≤ 15) =
    (program.filter Instruction.fetchable).find? (fun instruction => instruction.address == address) := by
  induction program with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : head.address = address
    · subst same
      by_cases fetchable : head.fetchable = true
      · have parts : head.address < word ∧ 0 < head.length ∧ head.length ≤ 15 := by
          simpa [Instruction.fetchable, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using fetchable
        simp [fetchable, parts]
      · have parts : ¬ (head.address < word ∧ 0 < head.length ∧ head.length ≤ 15) := by
          simpa [Instruction.fetchable, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using fetchable
        simp only [List.find?_cons, List.filter_cons, fetchable]
        simp only [beq_self_eq_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        rw [← ih]
        have : (decide (head.address < word) && decide (0 < head.length) && decide (head.length ≤ 15)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        simp [this]
    · have differs : (head.address == address) = false := by simpa using same
      by_cases fetchable : head.fetchable = true <;>
        simp [fetchable, differs, ih]

private theorem lookup_sound : ∀ {tree : InstructionTree} {address : Nat} {entry : Instruction},
    tree.lookup address = some entry → entry ∈ tree.toList ∧ entry.address = address
  | leaf, _, _, found => by simp [lookup] at found
  | node left middle right, address, entry, found => by
    simp only [lookup] at found
    split at found
    · obtain ⟨member, equal⟩ := lookup_sound found
      exact ⟨by simp [toList, member], equal⟩
    · split at found
      · obtain ⟨member, equal⟩ := lookup_sound found
        exact ⟨by simp [toList, member], equal⟩
      · cases found
        exact ⟨by simp [toList], by omega⟩

private theorem pairwise_of_increasing : ∀ entries : List Instruction,
    increasingAddresses entries = true → entries.Pairwise (fun first second => first.address < second.address)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | first :: second :: rest, increasing => by
    simp only [increasingAddresses, Bool.and_eq_true, decide_eq_true_eq] at increasing
    have tail := pairwise_of_increasing (second :: rest) increasing.2
    refine List.Pairwise.cons ?_ tail
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact increasing.1
    · exact Nat.lt_trans increasing.1 ((List.pairwise_cons.mp tail).1 other member)

private theorem lookup_complete : ∀ {tree : InstructionTree} {entry : Instruction},
    tree.toList.Pairwise (fun first second => first.address < second.address) →
    entry ∈ tree.toList → tree.lookup entry.address = some entry
  | leaf, _, _, member => by simp [toList] at member
  | node left middle right, entry, sorted, member => by
    simp only [toList, List.pairwise_append, List.pairwise_cons] at sorted
    obtain ⟨sortedLeft, ⟨afterMiddle, sortedRight⟩, across⟩ := sorted
    simp only [toList, List.mem_append, List.mem_cons] at member
    rcases member with member | rfl | member
    · have below := across entry member middle (by simp)
      simp [lookup, below, lookup_complete sortedLeft member]
    · simp [lookup]
    · have above := afterMiddle entry member
      have notBelow : ¬ entry.address < middle.address := by omega
      simp [lookup, notBelow, above, lookup_complete sortedRight member]

private theorem find?_sorted : ∀ {entries : List Instruction} {entry : Instruction},
    entries.Pairwise (fun first second => first.address < second.address) → entry ∈ entries →
    entries.find? (fun other => other.address == entry.address) = some entry
  | [], _, _, member => by simp at member
  | head :: rest, entry, sorted, member => by
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have below := (List.pairwise_cons.mp sorted).1 entry member
      have differs : (head.address == entry.address) = false := by simp; omega
      simp [differs, find?_sorted (List.pairwise_cons.mp sorted).2 member]

/-- Fetch through an index. -/
theorem Indexes.fetch_eq {tree : InstructionTree} {program : Program} (index : tree.Indexes program) (address : Nat) :
    program.fetch address = tree.lookup address := by
  have sorted := pairwise_of_increasing _ index.increasing
  rw [Program.fetch, find?_fetch, ← index.entries]
  cases found : tree.lookup address with
  | some entry =>
    obtain ⟨member, rfl⟩ := lookup_sound found
    exact find?_sorted sorted member
  | none =>
    cases searched : tree.toList.find? (fun other => other.address == address) with
    | none => rfl
    | some other =>
      have member := List.mem_of_find?_eq_some searched
      have same : other.address = address := by simpa using List.find?_some searched
      have := lookup_complete sorted member
      rw [same, found] at this
      cases this

theorem Indexes.nextAddress_eq {tree : InstructionTree} {program : Program} (index : tree.Indexes program) (address : Nat) :
    program.nextAddress address =
      ((tree.lookup address).map fun instruction => (address + instruction.length) % word).getD address := by
  rw [Program.nextAddress, index.fetch_eq]

theorem Indexes.instruction {tree : InstructionTree} {program : Program} (index : tree.Indexes program) {address : Nat} {operation : Op}
    (found : (tree.lookup address).map Instruction.op = some operation) :
    (program.fetch address).map Instruction.op = some operation := by
  rw [index.fetch_eq]
  exact found

end InstructionTree
end Rivet
end

public section
namespace Rivet
open Lean Meta Elab Command

namespace InstructionTree

/-- The elements of a list literal, unfolding definitions as needed. -/
private meta partial def listElements (list : Expr) : MetaM (Array Expr) := do
  let list ← whnf list
  if list.isAppOfArity ``List.nil 1 then return #[]
  unless list.isAppOfArity ``List.cons 3 do
    throwError "rivet_index: the program is not a concrete list of instructions"
  return #[list.getArg! 1] ++ (← listElements (list.getArg! 2))

/-- A balanced tree over `entries[low:high]`. -/
private meta partial def balanced (entries : Array Expr) (low high : Nat) : Expr :=
  if low ≥ high then mkConst ``InstructionTree.leaf else
  let middle := (low + high) / 2
  mkApp3 (mkConst ``InstructionTree.node) (balanced entries low middle) entries[middle]!
    (balanced entries (middle + 1) high)

end InstructionTree

/--
`rivet_index program` builds a balanced address index for a concrete program
constant, as `program.instructionTree`, and checks it once by evaluation, as
`program.instructionTree_indexes : program.instructionTree.Indexes program`.
`rivet_step` then looks up instructions in logarithmic rather than linear time.
The program's fetchable instructions must have strictly increasing addresses.
-/
syntax (name := rivetIndex) "rivet_index " ident : command

@[command_elab rivetIndex] meta def InstructionTree.elabRivetIndex : CommandElab := fun stx => do
  let program ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM do
    let elements ← InstructionTree.listElements (mkConst program)
    let mut entries : Array Expr := #[]
    let mut previous : Option Nat := none
    for element in elements do
      let element ← whnf element
      unless element.isAppOfArity ``Instruction.mk 3 do
        throwError "rivet_index: instruction {element} is not a literal"
      let some address ← (evalNat (element.getArg! 0)).run
        | throwError "rivet_index: address of {element} is not a numeral"
      let some length ← (evalNat (element.getArg! 1)).run
        | throwError "rivet_index: length of {element} is not a numeral"
      unless address < 2^64 && 0 < length && length ≤ 15 do continue
      if let some last := previous then
        unless last < address do
          throwError "rivet_index: fetchable instructions must have strictly increasing addresses \
            ({last} is followed by {address})"
      previous := some address
      entries := entries.push element
    let tree := InstructionTree.balanced entries 0 entries.size
    let treeName := program ++ `instructionTree
    addDecl (forceExpose := true) <| .defnDecl {
      name := treeName, levelParams := [], type := mkConst ``InstructionTree, value := tree,
      hints := .abbrev, safety := .safe }
    let indexType := mkApp2 (mkConst ``InstructionTree.Indexes) (mkConst treeName) (mkConst program)
    let entriesType ← mkEq (mkApp (mkConst ``InstructionTree.toList) (mkConst treeName))
      (← mkAppM ``List.filter #[mkConst ``Instruction.fetchable, mkConst program])
    let increasingType ← mkEq
      (mkApp (mkConst ``increasingAddresses) (mkApp (mkConst ``InstructionTree.toList) (mkConst treeName)))
      (mkConst ``Bool.true)
    let proof := mkApp4 (mkConst ``InstructionTree.Indexes.mk) (mkConst treeName) (mkConst program)
      (← mkExpectedTypeHint (← mkEqRefl (← mkAppM ``List.filter #[mkConst ``Instruction.fetchable, mkConst program])) entriesType)
      (← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) increasingType)
    addDecl <| .thmDecl {
      name := program ++ `instructionTree_indexes, levelParams := [], type := indexType, value := proof }

end Rivet
end
