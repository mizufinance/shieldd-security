import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0041
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810041
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0041.slots :=
 LegalWordAvoid281.checked_avoid _ 10716 10849 []
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810041

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810041.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810041.avoid
