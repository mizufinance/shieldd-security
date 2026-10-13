import ShielddSecurity.CapturedBooleanSlots208B0071
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserRecordAvoid362B41
theorem checked : CapturedBooleanSlots208B0071.slots.all (fun pair => decide
    (¬ (1504 ≤ pair.2 ∧ pair.2 < 1579) ∧ ¬ (1742 ≤ pair.2 ∧ pair.2 < 1817))) = true := by decide +kernel
end ShielddSecurity.UserRecordAvoid362B41

set_option pp.all true in
#check @ShielddSecurity.UserRecordAvoid362B41.checked
#print axioms ShielddSecurity.UserRecordAvoid362B41.checked
