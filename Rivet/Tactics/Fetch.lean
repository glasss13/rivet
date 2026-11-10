module
public import Rivet.Interpreter.Memory
public import Rivet.Laws.Program
-- `rivet_fetch`: proves which instruction a concrete program holds at an address.
public meta import Lean
-- The lookup routine is public but not exposed; its helpers are private.
public section
namespace Rivet
open Lean Meta Elab Tactic

namespace Fetch

private meta def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

meta def addressValue? (address : Expr) : MetaM (Option Nat) := do
  let address ← instantiateMVars address
  if let some ⟨_, value⟩ ← getBitVecValue? address then return some value.toNat
  if address.hasFVar || address.hasMVar then return none
  try
    let value ← withTransparency .default <| whnf (← mkAppM ``BitVec.toNat #[address])
    (evalNat value).run
  catch _ => return none

private meta def firstMatch (list : Expr) (pc : Nat) (limit : Nat := 0) : MetaM (Option Expr) := do
  let mut current := list
  let mut visited := 0
  repeat
    if limit != 0 && visited ≥ limit then return none
    current ← whnf current
    unless current.isAppOfArity ``List.cons 3 do return none
    let instruction ← whnf (current.getArg! 1)
    unless instruction.isAppOfArity ``Instruction.mk 3 do return none
    let some address ← addressValue? (instruction.getArg! 0) | return none
    let some length ← (evalNat (← whnf (instruction.getArg! 1))).run | return none
    if address == pc && 0 < length && length ≤ 15 then return some instruction
    current := current.getArg! 2
    visited := visited + 1
  return none

private meta def programOf (program : Expr) : MetaM Expr := do
  let program ← instantiateMVars program
  let image? := if program.isAppOfArity ``Image.program 1 then some program.appArg!
    else match program with
      | .proj ``Image 0 image => some image
      | _ => none
  let some image := image? | return program
  let image ← whnfD image
  return if image.isAppOfArity ``Image.mk 2 then image.getArg! 0 else program

meta def prove (original address : Expr) (pc : Nat) : MetaM (Option (Expr × Expr)) := withTransparency .all do
  let program ← programOf original
  -- State the result about the caller's program, so it matches their goal syntactically.
  let restate (instruction proof : Expr) : MetaM (Expr × Expr) := do
    let fetched ← mkAppM ``Program.fetch #[original, address]
    return (instruction, ← mkExpectedTypeHint proof (← mkEq fetched (← mkAppM ``Option.some #[instruction])))
  if let some name := program.constName? then
    let stepName := name ++ Name.mkSimple s!"from_{hex pc}"
    if (← getEnv).contains stepName then
      let same := mkApp2 (mkConst stepName) address (mkApp2 (mkConst ``BitVec.le_refl) (mkNatLit 64) address)
      let some (_, _, suffixFetch) := (← instantiateMVars (← inferType same)).eq? | return none
      let some instruction ← firstMatch (suffixFetch.appFn!.appArg!) pc (limit := 1) | return none
      let result ← mkAppM ``Option.some #[instruction]
      let head ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq suffixFetch result)
      return some (← restate instruction (← mkEqTrans same head))
  let some instruction ← firstMatch program pc | return none
  let result ← mkAppM ``Option.some #[instruction]
  let fetched ← mkAppM ``Program.fetch #[program, address]
  return some (← restate instruction (← mkExpectedTypeHint (← mkEqRefl result) (← mkEq fetched result)))

end Fetch

syntax (name := rivetFetch) "rivet_fetch" : tactic

@[tactic rivetFetch] meta def Fetch.evalRivetFetch : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, fetched, expected) := type.eq?
    | throwError "rivet_fetch: goal is not `program.fetch address = some instruction`"
  unless fetched.isAppOfArity ``Program.fetch 2 do
    throwError "rivet_fetch: goal is not `program.fetch address = some instruction`"
  let program := fetched.getArg! 0
  let address := fetched.getArg! 1
  let some pc ← Fetch.addressValue? address
    | evalTactic (← `(tactic| assumption))
  match ← Fetch.prove program address pc with
  | some (instruction, proof) =>
    unless ← isDefEq expected (← mkAppM ``Option.some #[instruction]) do
      throwError "rivet_fetch: the instruction at address {pc} is `{instruction.getArg! 2}`"
    goal.assign proof
    replaceMainGoal []
  | none => evalTactic (← `(tactic| assumption))

end Rivet
end
