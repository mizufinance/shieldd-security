import ShielddSecurity.CapturedBooleanSlots208B0033
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkAvoid501B22
theorem checked : CapturedBooleanSlots208B0033.slots.all (fun pair => decide
    (pair.2<4271 ∨ 4279< pair.2)) = true := by decide +kernel
end ShielddSecurity.AuthorizationRkAvoid501B22

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkAvoid501B22.checked
#print axioms ShielddSecurity.AuthorizationRkAvoid501B22.checked
