import ShielddSecurity.CapturedBooleanSlots208B0071
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedAvoid483B41
theorem checked : CapturedBooleanSlots208B0071.slots.all (fun pair => decide
    (pair.2<4019 ∨ 4270< pair.2)) = true := by decide +kernel
end ShielddSecurity.AuthorizationFixedAvoid483B41

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedAvoid483B41.checked
#print axioms ShielddSecurity.AuthorizationFixedAvoid483B41.checked
