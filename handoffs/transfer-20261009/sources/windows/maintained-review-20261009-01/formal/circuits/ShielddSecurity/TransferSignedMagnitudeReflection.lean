import ShielddSecurity.TransferSignedMagnitude

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferSignedMagnitudeReflection

/-- Bounded native amounts and the row-derived magnitude prevent field wrap.
At zero magnitude either Boolean sign gives the same integer consequence. -/
theorem integer_difference {F : Type} [Field F] [CharP F Scalar.modulus]
    (amounts : TransferSignedMagnitude.Inputs) (n : Nat) (sign : Bool)
    (bound : n < 2^129)
    (equation : (TransferSignedMagnitude.inputTotal amounts : F) -
      (TransferSignedMagnitude.outputTotal amounts : F) =
        if sign then -(n : F) else (n : F)) :
    (if sign then -(n : Int) else (n : Int)) =
      (TransferSignedMagnitude.inputTotal amounts : Int) -
        (TransferSignedMagnitude.outputTotal amounts : Int) := by
  have a := (amounts 0).isLt
  have b := (amounts 1).isLt
  have c := (amounts 2).isLt
  have d := (amounts 3).isLt
  have inputBound : TransferSignedMagnitude.inputTotal amounts < 2^129 := by
    unfold TransferSignedMagnitude.inputTotal
    omega
  have outputBound : TransferSignedMagnitude.outputTotal amounts < 2^129 := by
    unfold TransferSignedMagnitude.outputTotal
    omega
  have capacity : 2^130 < Scalar.modulus := by decide
  cases sign with
  | false =>
      simp only [Bool.false_eq_true, if_false] at equation ⊢
      have cast : (TransferSignedMagnitude.inputTotal amounts : F) =
          ((TransferSignedMagnitude.outputTotal amounts + n : Nat) : F) := by
        rw [Nat.cast_add, ← equation]
        ring
      have equal := bounded_cast_injective (F := F) (p := Scalar.modulus)
        (show TransferSignedMagnitude.inputTotal amounts < Scalar.modulus by omega)
        (show TransferSignedMagnitude.outputTotal amounts + n < Scalar.modulus by omega) cast
      omega
  | true =>
      simp only [if_true] at equation ⊢
      have cast : ((TransferSignedMagnitude.inputTotal amounts + n : Nat) : F) =
          (TransferSignedMagnitude.outputTotal amounts : F) := by
        rw [Nat.cast_add]
        calc
          (TransferSignedMagnitude.inputTotal amounts : F) + (n : F) =
            (TransferSignedMagnitude.outputTotal amounts : F) +
              ((TransferSignedMagnitude.inputTotal amounts : F) -
                (TransferSignedMagnitude.outputTotal amounts : F) + (n : F)) := by ring
          _ = (TransferSignedMagnitude.outputTotal amounts : F) := by
            rw [equation, neg_add_cancel, add_zero]
      have equal := bounded_cast_injective (F := F) (p := Scalar.modulus)
        (show TransferSignedMagnitude.inputTotal amounts + n < Scalar.modulus by omega)
        (show TransferSignedMagnitude.outputTotal amounts < Scalar.modulus by omega) cast
      omega

set_option pp.all true in
#check @integer_difference
#print axioms integer_difference

end ShielddSecurity.TransferSignedMagnitudeReflection
