import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0032
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810032
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0032.slots :=
 LegalWordAvoid281.checked_avoid _ 8317 8680 [8387,8551]
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810032

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810032.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810032.avoid
