import ShielddSecurity.CapturedBooleanSlots208B0084
import ShielddSecurity.FixedFamilyLayout545
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyAvoid546B54
theorem checked : CapturedBooleanSlots208B0084.slots.all (fun pair => FixedFamilyLayout545.outside pair.2) = true := by decide +kernel
end ShielddSecurity.FixedFamilyAvoid546B54

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyAvoid546B54.checked
#print axioms ShielddSecurity.FixedFamilyAvoid546B54.checked
