import ShielddSecurity.CapturedBooleanSlots208B0024
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroInverseAvoid331B16
theorem checked : CapturedBooleanSlots208B0024.slots.all (fun pair => decide
    (pair.2 ≠ 1111 ∧ pair.2 ≠ 1372)) = true := by decide +kernel
end ShielddSecurity.HighZeroInverseAvoid331B16

set_option pp.all true in
#check @ShielddSecurity.HighZeroInverseAvoid331B16.checked
#print axioms ShielddSecurity.HighZeroInverseAvoid331B16.checked
