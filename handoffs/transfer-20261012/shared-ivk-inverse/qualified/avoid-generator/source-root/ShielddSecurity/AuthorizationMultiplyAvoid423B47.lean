import ShielddSecurity.CapturedBooleanSlots208B0077
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationMultiplyAvoid423B47
theorem checked : CapturedBooleanSlots208B0077.slots.all (fun pair => decide
    (pair.2<2252 ∨ 3765< pair.2)) = true := by decide +kernel
end ShielddSecurity.AuthorizationMultiplyAvoid423B47

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyAvoid423B47.checked
#print axioms ShielddSecurity.AuthorizationMultiplyAvoid423B47.checked
