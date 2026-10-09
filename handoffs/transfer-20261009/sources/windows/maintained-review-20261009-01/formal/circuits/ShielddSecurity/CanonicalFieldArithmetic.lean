import ShielddSecurity.TransferReduction

set_option maxHeartbeats 200000

namespace ShielddSecurity.CanonicalFieldArithmetic

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Nat decoding of a field cast is reduction modulo the actual field modulus.
The codec contract supplies canonical representatives, including for extension
field exclusions. No arithmetic result is assumed as a codec law. -/
theorem decode_nat_cast (codec : TransferReduction.CanonicalField F) (n : Nat) :
    codec.decode (n : F) = n % Scalar.modulus := by
  have bounded : n % Scalar.modulus < Scalar.modulus := Nat.mod_lt _ (by decide)
  have cast : ((n % Scalar.modulus : Nat) : F) = (n : F) := by
    have division := congrArg (fun value : Nat => (value : F)) (Nat.mod_add_div n Scalar.modulus)
    simpa only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero F Scalar.modulus,
      zero_mul, add_zero] using division
  exact Scalar.canonical_representative_unique (n : F) (codec.decode (n : F))
    (n % Scalar.modulus) (codec.bounded _) bounded (codec.roundtrip _) cast

theorem decode_add (codec : TransferReduction.CanonicalField F) (left right : F) :
    codec.decode (left + right) = (codec.decode left + codec.decode right) % Scalar.modulus := by
  have cast : ((codec.decode left + codec.decode right : Nat) : F) = left + right := by
    rw [Nat.cast_add, codec.roundtrip, codec.roundtrip]
  rw [← cast]
  exact decode_nat_cast codec _

theorem decode_mul (codec : TransferReduction.CanonicalField F) (left right : F) :
    codec.decode (left * right) = (codec.decode left * codec.decode right) % Scalar.modulus := by
  have cast : ((codec.decode left * codec.decode right : Nat) : F) = left * right := by
    rw [Nat.cast_mul, codec.roundtrip, codec.roundtrip]
  rw [← cast]
  exact decode_nat_cast codec _

theorem decode_zero (codec : TransferReduction.CanonicalField F) : codec.decode 0 = 0 := by
  simpa only [Nat.cast_zero] using TransferReduction.decode_canonical_cast codec 0 (by decide)

set_option pp.all true in
#check @decode_nat_cast
#print axioms decode_nat_cast
set_option pp.all true in
#check @decode_add
#print axioms decode_add
set_option pp.all true in
#check @decode_mul
#print axioms decode_mul
set_option pp.all true in
#check @decode_zero
#print axioms decode_zero

end ShielddSecurity.CanonicalFieldArithmetic
