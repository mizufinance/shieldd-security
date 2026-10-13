import ShielddSecurity.CapturedBooleanSlots208B0014
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserRecordAvoid362B09
theorem checked : CapturedBooleanSlots208B0014.slots.all (fun pair => decide
    (¬ (1504 ≤ pair.2 ∧ pair.2 < 1579) ∧ ¬ (1742 ≤ pair.2 ∧ pair.2 < 1817))) = true := by decide +kernel
end ShielddSecurity.UserRecordAvoid362B09

set_option pp.all true in
#check @ShielddSecurity.UserRecordAvoid362B09.checked
#print axioms ShielddSecurity.UserRecordAvoid362B09.checked
