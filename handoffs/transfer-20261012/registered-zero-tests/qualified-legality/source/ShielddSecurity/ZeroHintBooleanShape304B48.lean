import ShielddSecurity.CapturedBooleanSlots208B0078
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ZeroHintBooleanShape304B48
theorem checked : CapturedBooleanSlots208B0078.slots.all (fun pair => decide
    (113 ≤ pair.2 → pair.2 < 135 → pair.2 % 2 = 1)) = true := by decide +kernel
end ShielddSecurity.ZeroHintBooleanShape304B48

set_option pp.all true in
#check @ShielddSecurity.ZeroHintBooleanShape304B48.checked
#print axioms ShielddSecurity.ZeroHintBooleanShape304B48.checked
