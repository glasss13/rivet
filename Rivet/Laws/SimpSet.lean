module
public meta import Lean
-- The `rivet` simp set, and the shared default for access side conditions.
public section

/-- The `rivet` simp set: proved equations for the closed definitions
(`MachineState.canRead`, `MachineState.canWrite`, `Address.evaluate`), with the word
lemmas that put concrete addresses in normal form, such as `s.registers .rbx - 8#64`.
Reduce with `simp only [rivet]`; extend it by tagging your own theorems `@[rivet]`. -/
register_simp_attr rivet

/-- The default for an access side condition (`readable`, `writable`, …): a hypothesis
that matches syntactically, or else the goal reduced by the `rivet` simp set, which
closes register and immediate operands outright, and then a syntactic match. It never
unfolds a definition by computation, so it fails with an ordinary error. -/
syntax (name := rivetAccess) "rivet_access" : tactic

macro_rules
  | `(tactic| rivet_access) =>
    `(tactic| first | with_reducible assumption | (simp only [rivet] <;> with_reducible assumption))

end
