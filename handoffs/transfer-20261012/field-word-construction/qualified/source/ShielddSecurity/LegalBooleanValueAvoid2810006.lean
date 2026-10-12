import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0006
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810006
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0006.slots :=
 LegalWordAvoid281.checked_avoid _ 1622 1860 [1742,1743,1750,1751,1767,1768]
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810006

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810006.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810006.avoid
