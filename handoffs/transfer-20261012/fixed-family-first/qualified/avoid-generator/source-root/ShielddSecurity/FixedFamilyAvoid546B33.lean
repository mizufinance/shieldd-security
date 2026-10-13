import ShielddSecurity.CapturedBooleanSlots208B0057
import ShielddSecurity.FixedFamilyLayout545
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyAvoid546B33
theorem checked : CapturedBooleanSlots208B0057.slots.all (fun pair => FixedFamilyLayout545.outside pair.2) = true := by decide +kernel
end ShielddSecurity.FixedFamilyAvoid546B33

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyAvoid546B33.checked
#print axioms ShielddSecurity.FixedFamilyAvoid546B33.checked
