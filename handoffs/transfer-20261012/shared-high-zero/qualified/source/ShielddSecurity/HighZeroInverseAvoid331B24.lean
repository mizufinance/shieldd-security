import ShielddSecurity.CapturedBooleanSlots208B0035
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroInverseAvoid331B24
theorem checked : CapturedBooleanSlots208B0035.slots.all (fun pair => decide
    (pair.2 ≠ 1111 ∧ pair.2 ≠ 1372)) = true := by decide +kernel
end ShielddSecurity.HighZeroInverseAvoid331B24

set_option pp.all true in
#check @ShielddSecurity.HighZeroInverseAvoid331B24.checked
#print axioms ShielddSecurity.HighZeroInverseAvoid331B24.checked
