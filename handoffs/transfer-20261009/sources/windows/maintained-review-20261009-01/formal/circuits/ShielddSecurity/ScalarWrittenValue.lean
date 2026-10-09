import ShielddSecurity.ScalarReductionSeed

set_option maxHeartbeats 100000

namespace ShielddSecurity.ScalarWrittenValue

variable {F : Type} [Field F]

/-- Weighted field value of the actual written bits. This uses the operation's
map law directly, without field-cast injectivity or a reconstruction premise. -/
theorem weighted_value (base rho : Nat → F) (start : Nat) (bits : List Bool)
    (preserved : ∀ column ∈ List.range' start bits.length,
      rho column = writeBits base start bits column) :
    eval rho (weighted (List.range' start bits.length) 1) = (binary bits : F) := by
  have mapped : (List.range' start bits.length).map rho =
      (List.range' start bits.length).map (writeBits base start bits) :=
    List.map_congr_left preserved
  rw [weighted_eval,mapped,writeBits_map,binary_cast]
  simp only [Int.cast_one,one_mul]

theorem remainder_value (base rho : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (start : Nat) (preserved : ∀ column ∈ List.range' start 252,
      rho column = writeBits base start (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column) :
    eval rho (weighted (List.range' start 252) 1) = (ScalarReductionSeed.remainder codec value : F) := by
  have bound : ScalarReductionSeed.remainder codec value < 2^252 :=
    (ScalarReductionCompletion.decoded_operands codec value).2.1.trans (by decide : Scalar.order < 2^252)
  have result := weighted_value base rho start (encodeBits 252 (ScalarReductionSeed.remainder codec value))
    (by simpa only [encodeBits_length] using preserved)
  simpa only [encodeBits_length,encodeBits_value 252 _ bound] using result

/-- Legality is stated on the globally decoded input hash, never on a witness
column or desired inverse. The original consumer value is derived above. -/
theorem remainder_nonzero [CharP F Scalar.modulus]
    (base rho : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (start : Nat) (preserved : ∀ column ∈ List.range' start 252,
      rho column = writeBits base start (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column)
    (legalInput : codec.decode value % Scalar.order ≠ 0) :
    eval rho (weighted (List.range' start 252) 1) ≠ 0 := by
  rw [remainder_value base rho codec value start preserved]
  intro zero
  have small : ScalarReductionSeed.remainder codec value < Scalar.modulus :=
    (ScalarReductionCompletion.decoded_operands codec value).2.1.trans (by decide : Scalar.order < Scalar.modulus)
  have equal := bounded_cast_injective (F := F) (p := Scalar.modulus) small (by decide : 0 < Scalar.modulus)
    (by simpa only [Nat.cast_zero] using zero)
  exact legalInput equal

set_option pp.all true in
#check @weighted_value
#print axioms weighted_value
set_option pp.all true in
#check @remainder_value
#print axioms remainder_value
set_option pp.all true in
#check @remainder_nonzero
#print axioms remainder_nonzero

end ShielddSecurity.ScalarWrittenValue
