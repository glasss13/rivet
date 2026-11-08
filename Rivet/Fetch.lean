module
public import Rivet.Syntax
public meta import Lean
-- The lookup routine is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace Fetch

private meta def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The first instruction of a concrete list that `Program.fetch` returns at `pc`,
found by walking the list (at most `limit` entries). Mirrors `Program.fetch`: the
address must equal `pc`, `pc` must be a 64-bit address, and the length 1 to 15. -/
private meta def firstMatch (list : Expr) (pc : Nat) (limit : Nat := 0) : MetaM (Option Expr) := do
  let mut current := list
  let mut visited := 0
  repeat
    if limit != 0 && visited ≥ limit then return none
    current ← whnf current
    unless current.isAppOfArity ``List.cons 3 do return none
    let instruction ← whnf (current.getArg! 1)
    unless instruction.isAppOfArity ``Instruction.mk 3 do return none
    let some address ← (evalNat (← whnf (instruction.getArg! 0))).run | return none
    let some length ← (evalNat (← whnf (instruction.getArg! 1))).run | return none
    if address == pc && pc < 2^64 && 0 < length && length ≤ 15 then return some instruction
    current := current.getArg! 2
    visited := visited + 1
  return none

/-- For a concrete program and address, the instruction `Program.fetch` returns and
a proof `program.fetch pc = some instruction`, checked by the kernel.

A generated program has a fact `program.from_<pc> : program.FetchesFrom suffix pc`
whose suffix starts with that instruction; the proof then evaluates only that one
entry, in time independent of the program size. Otherwise the list is searched. -/
meta def prove (program : Expr) (pc : Nat) : MetaM (Option (Expr × Expr)) := withTransparency .all do
  let address := mkNatLit pc
  if let some name := program.constName? then
    let stepName := name ++ Name.mkSimple s!"from_{hex pc}"
    if (← getEnv).contains stepName then
      let same := mkApp2 (mkConst stepName) address (mkApp (mkConst ``Nat.le_refl) address)
      let some (_, _, suffixFetch) := (← instantiateMVars (← inferType same)).eq? | return none
      let some instruction ← firstMatch (suffixFetch.appFn!.appArg!) pc (limit := 1) | return none
      let result ← mkAppM ``Option.some #[instruction]
      let head ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq suffixFetch result)
      return some (instruction, ← mkEqTrans same head)
  let some instruction ← firstMatch program pc | return none
  let result ← mkAppM ``Option.some #[instruction]
  let fetched ← mkAppM ``Program.fetch #[program, address]
  return some (instruction, ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq fetched result))

end Fetch

/--
`rivet_fetch` proves `InstructionAt program address length operation`, that is
`program.fetch address = some ⟨address, length, operation⟩`, for a concrete program
and address. An unknown `length` (or operation) is filled in from the program.
It is the default proof of every instruction contract's `code` argument.

For programs generated as suffix chains it takes time independent of the program
size; for other concrete programs it searches the list. Otherwise it falls back to
`assumption`, for abstract programs whose instructions are given as hypotheses.
-/
syntax (name := rivetFetch) "rivet_fetch" : tactic

@[tactic rivetFetch] meta def Fetch.evalRivetFetch : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, fetched, expected) := type.eq?
    | throwError "rivet_fetch: goal is not `program.fetch address = some instruction`"
  unless fetched.isAppOfArity ``Program.fetch 2 do
    throwError "rivet_fetch: goal is not `program.fetch address = some instruction`"
  let program := fetched.getArg! 0
  let some pc ← (evalNat (← whnfD (fetched.getArg! 1))).run
    | evalTactic (← `(tactic| assumption))
  match ← Fetch.prove program pc with
  | some (instruction, proof) =>
    unless ← isDefEq expected (← mkAppM ``Option.some #[instruction]) do
      throwError "rivet_fetch: the instruction at address {pc} is `{instruction.getArg! 2}`"
    goal.assign proof
    replaceMainGoal []
  | none => evalTactic (← `(tactic| assumption))

end Rivet
end
