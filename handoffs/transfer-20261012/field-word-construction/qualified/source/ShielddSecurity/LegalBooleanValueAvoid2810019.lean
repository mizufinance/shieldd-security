import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0019
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810019
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0019.slots :=
 LegalWordAvoid281.checked_avoid _ 5010 5182 []
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810019

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810019.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810019.avoid
