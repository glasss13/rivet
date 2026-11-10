module
public meta import Lean
-- The `rivet` simp set.
public section

/-- The `rivet` simp set: proved equations for the closed definitions
(`MachineState.canRead`, `MachineState.canWrite`, `Address.evaluate`,
`MachineState.readOperand`, `MachineState.writeOperand`),
register aliases' parents, and the word lemmas that put concrete addresses in normal
form, such as `s.registers .rbx - 8#64`.
Reduce with `simp only [rivet]`; extend it by tagging your own theorems `@[rivet]`. -/
register_simp_attr rivet

end
