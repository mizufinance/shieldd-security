import ShielddSecurity.CapturedBooleanSlots208B0068
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointAvoid406B38
theorem checked : CapturedBooleanSlots208B0068.slots.all (fun pair => decide
    (pair.2 ∉ [1980,1981,1982,1983,1984,1985,1986,1987,1993])) = true := by decide +kernel
end ShielddSecurity.AuthorizationPointAvoid406B38

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointAvoid406B38.checked
#print axioms ShielddSecurity.AuthorizationPointAvoid406B38.checked
