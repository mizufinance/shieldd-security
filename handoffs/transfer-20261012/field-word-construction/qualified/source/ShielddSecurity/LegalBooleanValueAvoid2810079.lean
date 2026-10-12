import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0079
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810079
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0079.slots :=
 LegalWordAvoid281.checked_avoid _ 20237 20456 []
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810079

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810079.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810079.avoid
