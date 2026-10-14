import ShielddSecurity.CapturedBooleanSlots208B0076
import ShielddSecurity.PayloadFamilyLayout559
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadFamilyAvoid560B46
theorem checked : CapturedBooleanSlots208B0076.slots.all (fun pair => PayloadFamilyLayout559.outside pair.2) = true := by decide +kernel
end ShielddSecurity.PayloadFamilyAvoid560B46

set_option pp.all true in
#check @ShielddSecurity.PayloadFamilyAvoid560B46.checked
#print axioms ShielddSecurity.PayloadFamilyAvoid560B46.checked
