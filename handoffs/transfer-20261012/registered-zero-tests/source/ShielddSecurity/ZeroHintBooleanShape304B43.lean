import ShielddSecurity.CapturedBooleanSlots208B0073
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ZeroHintBooleanShape304B43
theorem checked : CapturedBooleanSlots208B0073.slots.all (fun pair => decide
    (113 ≤ pair.2 → pair.2 < 135 → pair.2 % 2 = 1)) = true := by decide +kernel
end ShielddSecurity.ZeroHintBooleanShape304B43
