import ShielddSecurity.CapturedBooleanSlots208B0068
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationMultiplyAvoid423B38
theorem checked : CapturedBooleanSlots208B0068.slots.all (fun pair => decide
    (pair.2<2252 ∨ 3765< pair.2)) = true := by decide +kernel
end ShielddSecurity.AuthorizationMultiplyAvoid423B38

set_option pp.all true in
#check @ShielddSecurity.AuthorizationMultiplyAvoid423B38.checked
#print axioms ShielddSecurity.AuthorizationMultiplyAvoid423B38.checked
