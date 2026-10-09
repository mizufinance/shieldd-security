import ShielddSecurity.RuntimeTransferBalanceFinalAddCompletion
import ShielddSecurity.RuntimeTransferBalanceFinalAddSoundness

set_option maxHeartbeats 250000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceFinalAddRelation

theorem rows_same : RuntimeTransferBalanceFinalAddSoundness.rawRows =
    RuntimeTransferBalanceFinalAddCompletion.rawRows := by rfl

theorem output_same {F : Type} [Field F] (rho : Nat → F) :
    RuntimeTransferBalanceFinalAddSoundness.outputPoint rho =
      RuntimeTransferBalanceFinalAddCompletion.outputPoint rho := by rfl

/-- Only the final-add step is composed here. The preceding variable/H
relations must establish both input meanings on this same assignment. -/
theorem model_sum {F : Type} [Field F]
    [CharP F RuntimeTransferBalanceFinalAddCompletion.modulus]
    {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho RuntimeTransferBalanceFinalAddCompletion.rawRows)
    (sign : Bool)
    (signValue : eval rho RuntimeTransferBalanceFinalAddCompletion.negative =
      if sign then 1 else 0)
    (left right : J)
    (leftMeaning : RuntimeTransferBalanceFinalAddCompletion.unsignedPoint rho =
      model.coordinates left)
    (rightMeaning : RuntimeTransferBalanceFinalAddCompletion.blindedPoint rho =
      model.coordinates right)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (imaginarySquare : imaginary * imaginary = -1) :
    RuntimeTransferBalanceFinalAddCompletion.outputPoint rho =
      model.coordinates ((if sign then -left else left) + right) := by
  classical
  have raw : Satisfies rho RuntimeTransferBalanceFinalAddSoundness.rawRows := by
    rw [rows_same]
    exact satisfied
  have result := RuntimeTransferBalanceFinalAddSoundness.actual_rows_sound
    rho one raw sign signValue
  rw [output_same] at result
  change RuntimeTransferBalanceFinalAddCompletion.outputPoint rho =
    Group.affineAdd (RuntimeTransferBalanceFinalAddCompletion.d : F)
      (GroupSignedPoint.signed sign
        (RuntimeTransferBalanceFinalAddCompletion.unsignedPoint rho))
      (RuntimeTransferBalanceFinalAddCompletion.blindedPoint rho) at result
  rw [leftMeaning, rightMeaning] at result
  exact result.trans (GroupSignedPoint.final_native
    (RuntimeTransferBalanceFinalAddCompletion.d : F) imaginary model
    nonSquare imaginarySquare sign left right)

set_option pp.all true in
#check @rows_same
#print axioms rows_same
set_option pp.all true in
#check @output_same
#print axioms output_same
set_option pp.all true in
#check @model_sum
#print axioms model_sum

end ShielddSecurity.TransferBalanceFinalAddRelation
