import ShielddSecurity.CapturedBooleanSlots208B0087
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationMultiplyAvoid423B56
theorem checked : CapturedBooleanSlots208B0087.slots.all (fun pair => decide
    (pair.2<2252 ∨ 3765< pair.2)) = true := by decide +kernel
end ShielddSecurity.AuthorizationMultiplyAvoid423B56

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyAvoid423B56.checked
#print axioms ShielddSecurity.AuthorizationMultiplyAvoid423B56.checked
