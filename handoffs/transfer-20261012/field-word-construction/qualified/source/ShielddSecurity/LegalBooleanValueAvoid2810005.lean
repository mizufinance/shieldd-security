import ShielddSecurity.LegalWordAvoid281
import ShielddSecurity.CapturedBooleanSlots208B0005
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalBooleanValueAvoid2810005
theorem avoid : LegalWordAvoid281.Avoid CapturedBooleanSlots208B0005.slots :=
 LegalWordAvoid281.checked_avoid _ 1320 1621 [1374,1504,1505,1512,1513,1529,1530]
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ShielddSecurity.LegalBooleanValueAvoid2810005

set_option pp.all true in
#check @ShielddSecurity.LegalBooleanValueAvoid2810005.avoid
#print axioms ShielddSecurity.LegalBooleanValueAvoid2810005.avoid
