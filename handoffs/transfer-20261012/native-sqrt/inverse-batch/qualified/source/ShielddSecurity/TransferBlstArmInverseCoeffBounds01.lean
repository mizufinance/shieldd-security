import ShielddSecurity.TransferBlstArmInverseNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCoeffBounds01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
attribute [local irreducible] sourceFactorWalk

/-! Symbolic signed coefficient composition from initialized factor rows.
Both possible sign corrections preserve magnitude. Total factor counts bound
the entire coefficient pair without unrolling fixed 31/47-step walks. Actual
runtime batch observations/schedule, signed word multiply/store correspondence,
gcd termination and native execution remain separate obligations. -/

abbrev CoefficientPair := Int × Int
abbrev CoefficientBatch := Nat × Nat × Nat × Bool × Bool

def CoefficientBound (bound : Nat) (s : CoefficientPair) : Prop :=
  s.1.natAbs ≤ bound ∧ s.2.natAbs ≤ bound

def sourceCoefficientFlip (negative : Bool) (value : Int) : Int :=
  if negative then -value else value

theorem original_coefficient_sign_correction_preserves_entire_magnitude
    (negative : Bool) (value : Int) :
    (sourceCoefficientFlip negative value).natAbs=value.natAbs := by
  cases negative <;> simp [sourceCoefficientFlip]

def sourceCoefficientStep (batch : CoefficientBatch) (s : CoefficientPair) : CoefficientPair :=
  let factors := sourceFactorWalk batch.1 (sourceFactorInitial batch.2.1 batch.2.2.1)
  (sourceCoefficientFlip batch.2.2.2.1 (s.1*factors.f0+s.2*factors.g0),
    sourceCoefficientFlip batch.2.2.2.2 (s.1*factors.f1+s.2*factors.g1))

theorem initialized_factor_rows_derive_the_entire_next_coefficient_bound
    (batch : CoefficientBatch) (s : CoefficientPair) (bound : Nat) (bounded : CoefficientBound bound s) :
    CoefficientBound (bound*2^batch.1) (sourceCoefficientStep batch s) := by
  let factors := sourceFactorWalk batch.1 (sourceFactorInitial batch.2.1 batch.2.2.1)
  have rows := TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
    batch.1 batch.2.1 batch.2.2.1
  have first := TransferBlstArmInverseNorm01.bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    s.1 s.2 factors.f0 factors.g0 bound (2^batch.1) bounded.1 bounded.2 rows.1
  have second := TransferBlstArmInverseNorm01.bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    s.1 s.2 factors.f1 factors.g1 bound (2^batch.1) bounded.1 bounded.2 rows.2
  change (sourceCoefficientFlip batch.2.2.2.1 (s.1*factors.f0+s.2*factors.g0)).natAbs ≤ bound*2^batch.1 ∧
    (sourceCoefficientFlip batch.2.2.2.2 (s.1*factors.f1+s.2*factors.g1)).natAbs ≤ bound*2^batch.1
  rw [original_coefficient_sign_correction_preserves_entire_magnitude,
    original_coefficient_sign_correction_preserves_entire_magnitude]
  exact ⟨first,second⟩

def sourceCoefficientBits : List CoefficientBatch → Nat
  | [] => 0
  | batch::rest => batch.1+sourceCoefficientBits rest

def sourceCoefficientWalk : List CoefficientBatch → CoefficientPair → CoefficientPair
  | [],s => s
  | batch::rest,s => sourceCoefficientWalk rest (sourceCoefficientStep batch s)

theorem symbolic_entire_coefficient_walk_derives_the_summed_factor_count_bound
    (batches : List CoefficientBatch) (s : CoefficientPair) (bound : Nat) (bounded : CoefficientBound bound s) :
    CoefficientBound (bound*2^sourceCoefficientBits batches) (sourceCoefficientWalk batches s) := by
  induction batches generalizing s bound with
  | nil => simpa only [sourceCoefficientBits,sourceCoefficientWalk,pow_zero,mul_one] using bounded
  | cons batch rest ih =>
      have next := ih (sourceCoefficientStep batch s) (bound*2^batch.1)
        (initialized_factor_rows_derive_the_entire_next_coefficient_bound batch s bound bounded)
      have combined : (bound*2^batch.1)*2^sourceCoefficientBits rest=
          bound*2^sourceCoefficientBits (batch::rest) := by
        rw [sourceCoefficientBits,pow_add]
        ring
      rw [combined] at next
      exact next

def sourceCoefficientInitial : CoefficientPair := (1,0)

theorem original_unit_zero_coefficient_initialization_derives_the_entire_walk_magnitude_bound
    (batches : List CoefficientBatch) :
    CoefficientBound (2^sourceCoefficientBits batches) (sourceCoefficientWalk batches sourceCoefficientInitial) := by
  have initial : CoefficientBound 1 sourceCoefficientInitial := by
    change (1:Nat) ≤ 1 ∧ 0 ≤ 1
    decide
  have full := symbolic_entire_coefficient_walk_derives_the_summed_factor_count_bound batches sourceCoefficientInitial 1 initial
  simpa only [one_mul] using full

theorem factor_count_at_most_width_derives_both_entire_signed_coefficient_ranges
    (batches : List CoefficientBatch) (width : Nat) (budget : sourceCoefficientBits batches ≤ width) :
    let s := sourceCoefficientWalk batches sourceCoefficientInitial;
    -((2:Int)^width) ≤ s.1 ∧ s.1 ≤ (2:Int)^width ∧
      -((2:Int)^width) ≤ s.2 ∧ s.2 ≤ (2:Int)^width := by
  dsimp only
  have bounded := original_unit_zero_coefficient_initialization_derives_the_entire_walk_magnitude_bound batches
  have power := Nat.pow_le_pow_right Nat.zero_lt_two budget
  have first : ((sourceCoefficientWalk batches sourceCoefficientInitial).1.natAbs:Int) ≤ (2:Int)^width := by
    exact_mod_cast (bounded.1.trans power)
  have second : ((sourceCoefficientWalk batches sourceCoefficientInitial).2.natAbs:Int) ≤ (2:Int)^width := by
    exact_mod_cast (bounded.2.trans power)
  have upperFirst : (sourceCoefficientWalk batches sourceCoefficientInitial).1 ≤
      ((sourceCoefficientWalk batches sourceCoefficientInitial).1.natAbs:Int) := Int.le_natAbs
  have upperSecond : (sourceCoefficientWalk batches sourceCoefficientInitial).2 ≤
      ((sourceCoefficientWalk batches sourceCoefficientInitial).2.natAbs:Int) := Int.le_natAbs
  have lowerFirst : -(sourceCoefficientWalk batches sourceCoefficientInitial).1 ≤
      ((-(sourceCoefficientWalk batches sourceCoefficientInitial).1).natAbs:Int) := Int.le_natAbs
  have lowerSecond : -(sourceCoefficientWalk batches sourceCoefficientInitial).2 ≤
      ((-(sourceCoefficientWalk batches sourceCoefficientInitial).2).natAbs:Int) := Int.le_natAbs
  rw [Int.natAbs_neg] at lowerFirst lowerSecond
  repeat' constructor <;> omega

theorem factor_count_at_most_512_derives_both_entire_signed_coefficient_ranges
    (batches : List CoefficientBatch) (budget : sourceCoefficientBits batches ≤ 512) :
    let s := sourceCoefficientWalk batches sourceCoefficientInitial;
    -((2:Int)^512) ≤ s.1 ∧ s.1 ≤ (2:Int)^512 ∧
      -((2:Int)^512) ≤ s.2 ∧ s.2 ≤ (2:Int)^512 := by
  exact factor_count_at_most_width_derives_both_entire_signed_coefficient_ranges batches 512 budget

set_option pp.all true in
#check @CoefficientPair
#print axioms CoefficientPair
set_option pp.all true in
#check @CoefficientBatch
#print axioms CoefficientBatch
set_option pp.all true in
#check @CoefficientBound
#print axioms CoefficientBound
set_option pp.all true in
#check @sourceCoefficientFlip
#print axioms sourceCoefficientFlip
set_option pp.all true in
#check @original_coefficient_sign_correction_preserves_entire_magnitude
#print axioms original_coefficient_sign_correction_preserves_entire_magnitude
set_option pp.all true in
#check @sourceCoefficientStep
#print axioms sourceCoefficientStep
set_option pp.all true in
#check @initialized_factor_rows_derive_the_entire_next_coefficient_bound
#print axioms initialized_factor_rows_derive_the_entire_next_coefficient_bound
set_option pp.all true in
#check @sourceCoefficientBits
#print axioms sourceCoefficientBits
set_option pp.all true in
#check @sourceCoefficientWalk
#print axioms sourceCoefficientWalk
set_option pp.all true in
#check @symbolic_entire_coefficient_walk_derives_the_summed_factor_count_bound
#print axioms symbolic_entire_coefficient_walk_derives_the_summed_factor_count_bound
set_option pp.all true in
#check @sourceCoefficientInitial
#print axioms sourceCoefficientInitial
set_option pp.all true in
#check @original_unit_zero_coefficient_initialization_derives_the_entire_walk_magnitude_bound
#print axioms original_unit_zero_coefficient_initialization_derives_the_entire_walk_magnitude_bound
set_option pp.all true in
#check @factor_count_at_most_width_derives_both_entire_signed_coefficient_ranges
#print axioms factor_count_at_most_width_derives_both_entire_signed_coefficient_ranges
set_option pp.all true in
#check @factor_count_at_most_512_derives_both_entire_signed_coefficient_ranges
#print axioms factor_count_at_most_512_derives_both_entire_signed_coefficient_ranges
end ShielddSecurity.TransferBlstArmInverseCoeffBounds01
