import ShielddSecurity.TransferFfFieldApi01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfEulerCriterion01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferSqrtProducerField01
open TransferSqrtProducerLoop01
open TransferFfWordLoop01
open TransferFfActiveCompleteness01
open TransferFfFieldApi01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

theorem source_initial_residue_half_power_is_the_exact_euler_power
    (input : TransferCanonicalWordEquality01.CanonicalScalar) :
    sourceFieldValue (sourceSqrtInitial input).b ^ (2^31) =
      sourceFieldValue input ^ (nullifierModulus/2) := by
  rw [source_sqrt_initial_residue_has_exact_odd_power,← pow_mul]
  have count : ((nullifierModulus-1)/2^32)*(2^31) = nullifierModulus/2 := by decide +kernel
  rw [count]

theorem actual_ff_order_progress_derives_a_root_from_positive_euler_power
    (value : ZMod nullifierModulus) (positive : value ^ (nullifierModulus/2) = 1) : IsSquare value := by
  let input := fieldScalar value
  have meaning : sourceFieldValue input = value := actual_source_word_constructor_projects_to_every_field_input value
  have bound : sourceFieldValue (sourceSqrtInitial input).b ^ (2^31) = 1 := by
    rw [source_initial_residue_half_power_is_the_exact_euler_power,meaning]
    exact positive
  have ready : Ready (sourceFieldValue input) 32 (stateMeaning (sourceSqrtInitial input)) := by
    right
    refine ⟨⟨by change 1 < 32; decide,?_,bound,?_,?_⟩,by change 32 ≤ 32; decide⟩
    · exact source_sqrt_initial_candidate_square_equals_input_times_initial_residue input
    · exact source_root_of_unity_has_exact_power_and_half_power.1
    · exact source_root_of_unity_has_exact_power_and_half_power.2
  have finished := exact_descending_outer_loop_finishes_every_ready_state (sourceFieldValue input) 32 _ ready
  have projection := actual_source_sqrt_loop_has_the_exact_field_and_unsigned_index_meaning input
  change stateMeaning (sourceSqrtFinalState input) =
    FfFinishedPhase296.outerLoop (descendingRounds 32) (stateMeaning (sourceSqrtInitial input)) at projection
  rw [← projection] at finished
  have root : sourceFieldValue (sourceSqrtPayload input) ^ 2 = value := by
    simpa only [sourceSqrtPayload,stateMeaning,pow_two,meaning] using finished.1
  exact ⟨sourceFieldValue (sourceSqrtPayload input),by simpa only [pow_two] using root.symm⟩

theorem every_nonzero_square_has_positive_euler_power (value : ZMod nullifierModulus)
    (nonzero : value ≠ 0) (square : IsSquare value) : value ^ (nullifierModulus/2) = 1 := by
  have meaning := actual_source_word_constructor_projects_to_every_field_input value
  have inputNonzero : sourceFieldValue (fieldScalar value) ≠ 0 := by simpa only [meaning] using nonzero
  have inputSquare : IsSquare (sourceFieldValue (fieldScalar value)) := by simpa only [meaning] using square
  have bound := every_nonzero_square_input_derives_the_initial_half_order_bound (fieldScalar value) inputNonzero inputSquare
  simpa only [source_initial_residue_half_power_is_the_exact_euler_power,meaning] using bound

theorem every_nonzero_field_value_has_the_exact_fermat_power (value : ZMod nullifierModulus)
    (nonzero : value ≠ 0) : value ^ (nullifierModulus-1) = 1 := by
  let unit : (ZMod nullifierModulus)ˣ := Units.mk0 value nonzero
  have cardinality : Fintype.card (ZMod nullifierModulus)ˣ = nullifierModulus-1 := by
    rw [Fintype.card_units,ZMod.card]
  have unitPower : unit ^ (nullifierModulus-1) = 1 := by
    rw [← cardinality]
    exact pow_card_eq_one
  have projected := congrArg (fun u : (ZMod nullifierModulus)ˣ => (u : ZMod nullifierModulus)) unitPower
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,unit,Units.val_mk0] using projected

theorem every_nonsquare_has_negative_euler_power (value : ZMod nullifierModulus)
    (nonsquare : ¬ IsSquare value) : value ^ (nullifierModulus/2) = -1 := by
  have nonzero : value ≠ 0 := by
    intro zero
    exact nonsquare ⟨0,by simp only [zero,mul_zero]⟩
  apply TransferFfActiveAlgebra01.square_one_and_non_one_imply_minus_one
  · rw [← pow_mul]
    have count : (nullifierModulus/2)*2 = nullifierModulus-1 := by decide +kernel
    rw [count]
    exact every_nonzero_field_value_has_the_exact_fermat_power value nonzero
  · exact fun positive => nonsquare (actual_ff_order_progress_derives_a_root_from_positive_euler_power value positive)

theorem every_negative_euler_power_value_is_nonsquare (value : ZMod nullifierModulus)
    (negative : value ^ (nullifierModulus/2) = -1) : ¬ IsSquare value := by
  have nonzero : value ≠ 0 := by
    intro zero
    have bad : (0 : ZMod nullifierModulus) = -1 := by
      simpa only [zero,zero_pow (by decide : nullifierModulus/2 ≠ 0)] using negative
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod nullifierModulus) ≠ 0)) bad.symm
  intro square
  have positive := every_nonzero_square_has_positive_euler_power value nonzero square
  have different : (-1 : ZMod nullifierModulus) ≠ 1 := by decide +kernel
  exact different (negative.symm.trans positive)

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @source_initial_residue_half_power_is_the_exact_euler_power
#print axioms source_initial_residue_half_power_is_the_exact_euler_power
set_option pp.all true in
#check @actual_ff_order_progress_derives_a_root_from_positive_euler_power
#print axioms actual_ff_order_progress_derives_a_root_from_positive_euler_power
set_option pp.all true in
#check @every_nonzero_square_has_positive_euler_power
#print axioms every_nonzero_square_has_positive_euler_power
set_option pp.all true in
#check @every_nonzero_field_value_has_the_exact_fermat_power
#print axioms every_nonzero_field_value_has_the_exact_fermat_power
set_option pp.all true in
#check @every_nonsquare_has_negative_euler_power
#print axioms every_nonsquare_has_negative_euler_power
set_option pp.all true in
#check @every_negative_euler_power_value_is_nonsquare
#print axioms every_negative_euler_power_value_is_nonsquare
end ShielddSecurity.TransferFfEulerCriterion01
