import ShielddSecurity.RuntimeTransferSignedBalanceSoundness
import ShielddSecurity.TransferSignedMagnitudeReflection

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferSignedBalanceRelation

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Amount meanings are the four preceding range/source obligations, on this
same assignment. Their desired signed net is a conclusion. -/
theorem amount_difference (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs)
    (nativeAmounts : ∀ i, rho (RuntimeTransferSignedBalanceCompletion.amountColumns i) =
      ((amounts i).val : F)) :
    eval rho RuntimeTransferSignedBalanceCompletion.difference =
      (TransferSignedMagnitude.inputTotal amounts : F) -
        (TransferSignedMagnitude.outputTotal amounts : F) := by
  have zero : rho 4281 = ((amounts 0).val : F) := nativeAmounts 0
  have first : rho 4534 = ((amounts 1).val : F) := nativeAmounts 1
  have second : rho 4789 = ((amounts 2).val : F) := nativeAmounts 2
  have third : rho 6194 = ((amounts 3).val : F) := nativeAmounts 3
  have expression := Compiler.canonical_equal (p := Scalar.modulus) rho
    RuntimeTransferSignedBalanceCompletion.difference
    [(4281,1),(4534,1),(4789,-1),(6194,-1)] (by decide)
  rw [expression]
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,
    zero,first,second,third,TransferSignedMagnitude.inputTotal,
    TransferSignedMagnitude.outputTotal,Nat.cast_add]
  ring

/-- The circuit-selected sign may differ at zero; its signed integer value
always agrees with the exact bounded native amount difference. -/
theorem sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (amounts : TransferSignedMagnitude.Inputs)
    (nativeAmounts : ∀ i, rho (RuntimeTransferSignedBalanceCompletion.amountColumns i) =
      ((amounts i).val : F))
    (satisfied : Satisfies rho RuntimeTransferSignedBalanceCompletion.rawRows) :
    ∃ n : Nat, ∃ sign : Bool, n < 2^129 ∧ (n : F) = rho 21712 ∧
      rho 21711 = (if sign then 1 else 0) ∧
      (if sign then -(n : Int) else (n : Int)) =
        (TransferSignedMagnitude.inputTotal amounts : Int) -
          (TransferSignedMagnitude.outputTotal amounts : Int) := by
  obtain ⟨n,sign,bound,value,signValue,equation⟩ :=
    RuntimeTransferSignedBalanceSoundness.actual_rows_sound rho four satisfied
  have nativeEquation := (amount_difference rho amounts nativeAmounts).symm.trans equation
  exact ⟨n,sign,bound,value,signValue,
    TransferSignedMagnitudeReflection.integer_difference amounts n sign bound nativeEquation⟩

set_option pp.all true in
#check @amount_difference
#print axioms amount_difference
set_option pp.all true in
#check @sound
#print axioms sound

end ShielddSecurity.TransferSignedBalanceRelation
