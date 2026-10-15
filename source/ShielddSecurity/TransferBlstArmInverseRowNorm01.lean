import ShielddSecurity.TransferBlstArmInverseScaledInverse01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowNorm01
open TransferBlstArmInverseRowCompose01 (SourceLinearRows sourceComposeRows sourceIdentityRows)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)

/-! Small reusable coefficient row-sum bounds. Sign correction preserves the
norm and matrix composition multiplies bounds. These are integer statements;
finite word encoding and native carry/sign producers remain separate. -/

def SourceLinearRowsBound (bound : Nat) (rows : SourceLinearRows) : Prop :=
  rows.f0.natAbs + rows.g0.natAbs ≤ bound ∧ rows.f1.natAbs + rows.g1.natAbs ≤ bound

theorem source_magnitude_sign_has_exact_natural_magnitude_one
    (value : Int) : (sourceMagnitudeSign value).natAbs = 1 := by
  unfold sourceMagnitudeSign
  split <;> rfl

theorem simultaneous_source_row_sign_correction_preserves_its_entire_row_sum
    (value f g : Int) :
    (sourceMagnitudeSign value * f).natAbs + (sourceMagnitudeSign value * g).natAbs = f.natAbs + g.natAbs := by
  simp only [Int.natAbs_mul, source_magnitude_sign_has_exact_natural_magnitude_one, Nat.one_mul]

theorem two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound
    (oldF0 oldG0 oldF1 oldG1 nextF nextG : Int) (oldBound nextBound : Nat)
    (left : oldF0.natAbs + oldG0.natAbs ≤ oldBound)
    (right : oldF1.natAbs + oldG1.natAbs ≤ oldBound)
    (next : nextF.natAbs + nextG.natAbs ≤ nextBound) :
    (nextF * oldF0 + nextG * oldF1).natAbs + (nextF * oldG0 + nextG * oldG1).natAbs ≤ oldBound * nextBound := by
  calc
    _ ≤ ((nextF * oldF0).natAbs + (nextG * oldF1).natAbs) +
        ((nextF * oldG0).natAbs + (nextG * oldG1).natAbs) :=
      Nat.add_le_add (Int.natAbs_add_le _ _) (Int.natAbs_add_le _ _)
    _ = nextF.natAbs * (oldF0.natAbs + oldG0.natAbs) + nextG.natAbs * (oldF1.natAbs + oldG1.natAbs) := by
      simp only [Int.natAbs_mul]
      ring1
    _ ≤ nextF.natAbs * oldBound + nextG.natAbs * oldBound :=
      Nat.add_le_add (Nat.mul_le_mul_left _ left) (Nat.mul_le_mul_left _ right)
    _ = oldBound * (nextF.natAbs + nextG.natAbs) := by ring1
    _ ≤ oldBound * nextBound := Nat.mul_le_mul_left _ next

theorem exact_coefficient_row_composition_derives_the_product_of_both_row_sum_bounds
    (previous next : SourceLinearRows) (oldBound nextBound : Nat)
    (old : SourceLinearRowsBound oldBound previous) (step : SourceLinearRowsBound nextBound next) :
    SourceLinearRowsBound (oldBound * nextBound) (sourceComposeRows previous next) := by
  constructor
  · exact two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound _ _ _ _ _ _ _ _ old.1 old.2 step.1
  · exact two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound _ _ _ _ _ _ _ _ old.1 old.2 step.2

theorem original_identity_coefficient_rows_have_both_row_sums_at_most_one :
    SourceLinearRowsBound 1 sourceIdentityRows := by
  change 1 + 0 ≤ 1 ∧ 0 + 1 ≤ 1
  decide +kernel

set_option pp.all true in
#check @SourceLinearRowsBound
#print axioms SourceLinearRowsBound
set_option pp.all true in
#check @source_magnitude_sign_has_exact_natural_magnitude_one
#print axioms source_magnitude_sign_has_exact_natural_magnitude_one
set_option pp.all true in
#check @simultaneous_source_row_sign_correction_preserves_its_entire_row_sum
#print axioms simultaneous_source_row_sign_correction_preserves_its_entire_row_sum
set_option pp.all true in
#check @two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound
#print axioms two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound
set_option pp.all true in
#check @exact_coefficient_row_composition_derives_the_product_of_both_row_sum_bounds
#print axioms exact_coefficient_row_composition_derives_the_product_of_both_row_sum_bounds
set_option pp.all true in
#check @original_identity_coefficient_rows_have_both_row_sums_at_most_one
#print axioms original_identity_coefficient_rows_have_both_row_sums_at_most_one
end ShielddSecurity.TransferBlstArmInverseRowNorm01
