import ShielddSecurity.CapturedBooleanSlots208B0085
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserSubgroupAvoid353B55
theorem checked : CapturedBooleanSlots208B0085.slots.all (fun pair => decide
    (¬ (1504 ≤ pair.2 ∧ pair.2 < 1528) ∧ ¬ (1742 ≤ pair.2 ∧ pair.2 < 1766))) = true := by decide +kernel
end ShielddSecurity.UserSubgroupAvoid353B55

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupAvoid353B55.checked
#print axioms ShielddSecurity.UserSubgroupAvoid353B55.checked
