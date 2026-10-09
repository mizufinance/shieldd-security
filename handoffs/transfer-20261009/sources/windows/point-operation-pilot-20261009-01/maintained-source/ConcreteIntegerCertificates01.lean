import ShielddSecurity.ConcreteEdwardsParameters01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteIntegerCertificates01
open ConcreteJubjubField01

/-- A kernel-checked integer multiple establishes equality in the exact field. -/
theorem field_eq (left right multiple : Int)
    (certificate : left = right + multiple * (Scalar.modulus : Int)) :
    (left : F) = (right : F) := by
  have cast := congrArg (fun value : Int => (value : F)) certificate
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    mul_zero, add_zero] using cast

theorem field_nonzero (value inverse multiple : Int)
    (certificate : value * inverse = 1 + multiple * (Scalar.modulus : Int)) :
    (value : F) ≠ 0 := by
  have product : (value : F) * (inverse : F) = 1 := by
    simpa only [Int.cast_mul, Int.cast_one] using field_eq _ _ multiple certificate
  intro zero
  rw [zero, zero_mul] at product
  exact zero_ne_one product

end ShielddSecurity.ConcreteIntegerCertificates01
