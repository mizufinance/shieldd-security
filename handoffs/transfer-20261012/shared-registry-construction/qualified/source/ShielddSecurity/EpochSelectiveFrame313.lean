import ShielddSecurity.CapturedEpochNonzero61
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.EpochSelectiveFrame313
variable {F : Type} [Field F]
theorem primitive_frame (rho sigma : Nat → F) (epoch : sigma 34 = rho 34)
    (control : sigma 10 = rho 10) (indicator : sigma 113 = rho 113) (inverse : sigma 114 = rho 114)
    (primitive : CapturedEpochNonzero61.Primitive rho) : CapturedEpochNonzero61.Primitive sigma := by
  unfold CapturedEpochNonzero61.Primitive
  rw [epoch,control,indicator,inverse]
  exact primitive
end ShielddSecurity.EpochSelectiveFrame313
set_option pp.all true in
#check @ShielddSecurity.EpochSelectiveFrame313.primitive_frame
#print axioms ShielddSecurity.EpochSelectiveFrame313.primitive_frame
