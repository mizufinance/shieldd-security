import ShielddSecurity.CapturedBooleanSlots208B0032
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroInverseAvoid331B21
theorem checked : CapturedBooleanSlots208B0032.slots.all (fun pair => decide
    (pair.2 ≠ 1111 ∧ pair.2 ≠ 1372)) = true := by decide +kernel
end ShielddSecurity.HighZeroInverseAvoid331B21

set_option pp.all true in
#check @ShielddSecurity.HighZeroInverseAvoid331B21.checked
#print axioms ShielddSecurity.HighZeroInverseAvoid331B21.checked
