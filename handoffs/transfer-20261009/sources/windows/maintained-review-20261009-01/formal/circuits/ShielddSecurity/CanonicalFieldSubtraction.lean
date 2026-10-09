import ShielddSecurity.CanonicalFieldArithmetic

set_option maxHeartbeats 200000

namespace ShielddSecurity.CanonicalFieldSubtraction

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Decode subtraction using canonical natural representatives. The additional
modulus prevents truncated natural subtraction before the final reduction. -/
theorem decode_sub (codec : TransferReduction.CanonicalField F) (left right : F) :
    codec.decode (left - right) =
      (codec.decode left % Scalar.modulus + Scalar.modulus -
        codec.decode right % Scalar.modulus) % Scalar.modulus := by
  have leftBound := codec.bounded left
  have rightBound := codec.bounded right
  have noTruncation : codec.decode right ≤ codec.decode left + Scalar.modulus := by omega
  have cast : ((codec.decode left + Scalar.modulus - codec.decode right : Nat) : F) =
      left - right := by
    rw [Nat.cast_sub noTruncation, Nat.cast_add, CharP.cast_eq_zero F Scalar.modulus,
      add_zero, codec.roundtrip, codec.roundtrip]
  rw [Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound, ← cast]
  exact CanonicalFieldArithmetic.decode_nat_cast codec _

set_option pp.all true in
#check @decode_sub
#print axioms decode_sub

end ShielddSecurity.CanonicalFieldSubtraction
