import ShielddSecurity.RuntimeBalanceVariableSequenceSoundness
import ShielddSecurity.TransferSignedBalanceRelation
import ShielddSecurity.TransferBalanceBlindingCommittedRelation
import ShielddSecurity.TransferBalanceFinalAddRelation

set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferBalanceGroupRelation

def rows : List Row := RuntimeTransferSignedBalanceCompletion.rawRows ++
  (RuntimeBalanceVariableSequence.ownedRows 0 ++
    (TransferBalanceBlindingCommittedRelation.rows ++ RuntimeTransferBalanceFinalAddCompletion.rawRows))

theorem unsigned_input {F : Type} [Field F] (rho : Nat → F) :
    RuntimeTransferBalanceFinalAddCompletion.unsignedPoint rho =
      RuntimeBalanceVariableSequenceSoundness.outputPoint rho := rfl

theorem blinding_input {F : Type} [Field F] [CharP F Scalar.modulus] (rho : Nat → F) :
    GroupFixedCircuitCompletion.point rho TransferBalanceBlindingCanonicalFixedRelation.endpoint =
      RuntimeTransferBalanceFinalAddCompletion.blindedPoint rho := by
  apply congrArg₂ Group.Point.mk
  · exact Compiler.canonical_equal rho _ _ (by decide)
  · exact Compiler.canonical_equal rho _ _ (by decide)

/-- The native amount and generator meanings remain explicit source joins.
The signed net, both scalar multiples and the final commitment follow from
their captured physical rows on this same arbitrary assignment. -/
theorem sound {F J : Type} [Field F] [AddCommGroup J] [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (model : Group.StandardCurveModel J (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (asset blindingBase : J)
    (assetMeaning : RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho = model.coordinates asset)
    (blindingMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates blindingBase)
    (amounts : TransferSignedMagnitude.Inputs)
    (amountMeanings : ∀ i, rho (RuntimeTransferSignedBalanceCompletion.amountColumns i) = ((amounts i).val : F))
    (satisfied : Satisfies rho rows) :
    ∃ b : Nat, b < Scalar.order ∧ (b : F) = rho 2 ∧
      RuntimeTransferBalanceFinalAddCompletion.outputPoint rho = model.coordinates
        (((TransferSignedMagnitude.inputTotal amounts : Int) -
          (TransferSignedMagnitude.outputTotal amounts : Int)) • asset + b • blindingBase) := by
  have signedRows : Satisfies rho RuntimeTransferSignedBalanceCompletion.rawRows := by
    intro row member; exact satisfied row (List.mem_append_left _ member)
  have variableRows : Satisfies rho (RuntimeBalanceVariableSequence.ownedRows 0) := by
    intro row member; exact satisfied row (List.mem_append_right _ (List.mem_append_left _ member))
  have blindingRows : Satisfies rho TransferBalanceBlindingCommittedRelation.rows := by
    intro row member
    exact satisfied row (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member)))
  have finalRows : Satisfies rho RuntimeTransferBalanceFinalAddCompletion.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member)))
  obtain ⟨n,nBound,nValue,variableMeaning⟩ := RuntimeBalanceVariableSequenceSoundness.actual_scalar rho one linked
    four imaginary nonSquare imaginarySquare model asset assetMeaning signedRows variableRows
  obtain ⟨sign,signValue,fieldDifference⟩ := RuntimeTransferSignedBalanceSoundness.signed_from_actual rho four signedRows
  have difference : eval rho RuntimeTransferSignedBalanceCompletion.difference =
      if sign then -(n : F) else (n : F) := by
    rw [fieldDifference,← nValue]
    cases sign <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring
  have nativeEquation := (TransferSignedBalanceRelation.amount_difference rho amounts amountMeanings).symm.trans difference
  have integerDifference := TransferSignedMagnitudeReflection.integer_difference amounts n sign nBound nativeEquation
  have blinded := TransferBalanceBlindingCommittedRelation.sound model rho blindingBase one four imaginary
    nonSquare imaginarySquare blindingMeaning blindingRows
  let b := binary (RuntimeBalanceBlindingCanonical.decodedBits rho)
  have unsignedMeaning : RuntimeTransferBalanceFinalAddCompletion.unsignedPoint rho = model.coordinates (n • asset) := by
    rw [unsigned_input]; exact variableMeaning
  have blindedMeaning : RuntimeTransferBalanceFinalAddCompletion.blindedPoint rho = model.coordinates (b • blindingBase) :=
    (blinding_input rho).symm.trans blinded.2.2
  have negativeMeaning : eval rho RuntimeTransferBalanceFinalAddCompletion.negative = if sign then 1 else 0 := by
    simpa only [RuntimeTransferBalanceFinalAddCompletion.negative,eval,Int.cast_one,one_mul,add_zero] using signValue
  have final := TransferBalanceFinalAddRelation.model_sum model rho one finalRows sign negativeMeaning
    (n • asset) (b • blindingBase) unsignedMeaning blindedMeaning imaginary nonSquare imaginarySquare
  have signedMeaning : (if sign then -(n • asset) else n • asset) =
      ((TransferSignedMagnitude.inputTotal amounts : Int) -
        (TransferSignedMagnitude.outputTotal amounts : Int)) • asset := by
    rw [← integerDifference]
    cases sign <;> simp only [Bool.false_eq_true,if_false,if_true,neg_zsmul,natCast_zsmul]
  rw [signedMeaning] at final
  exact ⟨b,blinded.1,blinded.2.1,final⟩

set_option pp.all true in
#check @unsigned_input
#print axioms unsigned_input
set_option pp.all true in
#check @blinding_input
#print axioms blinding_input
set_option pp.all true in
#check @sound
#print axioms sound
end ShielddSecurity.TransferBalanceGroupRelation
