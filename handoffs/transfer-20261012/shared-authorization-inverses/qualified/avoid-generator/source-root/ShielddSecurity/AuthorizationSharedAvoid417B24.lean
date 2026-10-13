import ShielddSecurity.CapturedBooleanSlots208B0035
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedAvoid417B24
theorem checked : CapturedBooleanSlots208B0035.slots.all (fun pair => decide
    (pair.2 ∉ [1988,1989,1990,1991,1992])) = true := by decide +kernel
end ShielddSecurity.AuthorizationSharedAvoid417B24

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedAvoid417B24.checked
#print axioms ShielddSecurity.AuthorizationSharedAvoid417B24.checked
