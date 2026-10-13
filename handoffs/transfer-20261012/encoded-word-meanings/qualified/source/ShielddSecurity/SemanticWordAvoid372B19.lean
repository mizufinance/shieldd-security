import ShielddSecurity.CapturedBooleanSlots208B0030
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticWordAvoid372B19
theorem checked : CapturedBooleanSlots208B0030.slots.all (fun pair => decide
    (pair.2 ∉ [1994,1995,3766,4281,4411,4534,4664,4789,4930,6194,6334,7608,7609,7741,7742,8256,8387,8551,10083,11611,13629,14891,16153,19848,19849,21712])) = true := by decide +kernel
end ShielddSecurity.SemanticWordAvoid372B19

set_option pp.all true in
#check @ShielddSecurity.SemanticWordAvoid372B19.checked
#print axioms ShielddSecurity.SemanticWordAvoid372B19.checked
