import ShielddSecurity.TransferCommonwareSqrtLoop01
import ShielddSecurity.TransferFfFieldApi01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareSqrtComplete01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSqrtProducerField01
open TransferSqrtProducerLoop01
open TransferFfWordLoop01
open TransferFfSqrtComplete01
open TransferFfFieldApi01
open TransferCommonwareSqrtLoop01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

def sourceCommonwareExponent : Vector UInt64 4 :=
  #v[0x7fff_2dff_8000_0000,0x04d0_ec02_a9de_d201,
    0x94ce_bea4_199c_ec04,0x0000_0000_39f6_d3a9]

def sourceCommonwareRoot : ZMod nullifierModulus :=
  (montgomeryValue #v[0xb9b5_8d8c_5f0e_466a,0x5b1b_4c80_1819_d7ec,
    0x0af5_3ae3_52a3_1e64,0x5bf3_adda_19e9_b27b] : ZMod nullifierModulus)

theorem exact_commonware_exponent_is_the_successor_of_the_ff_initial_power :
    packWords sourceCommonwareExponent.toList =
      ((nullifierModulus-1)/2^32-1)/2+1 := by decide

theorem exact_commonware_root_literal_has_the_qualified_field_value :
    sourceCommonwareRoot = sourceFieldValue (TransferScalarPublicConstants01.sourceConstant .rootOfUnity) := rfl

def sourceInitial (input : CanonicalScalar) : FfFinishedPhase296.State (ZMod nullifierModulus) :=
  let value := sourceFieldValue input
  let r := value ^ packWords sourceCommonwareExponent.toList
  ⟨r,(r*r)*value⁻¹,sourceCommonwareRoot,32⟩

def sourceCommonwareFieldSqrt (input : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  if input = 0 then some 0 else sourceLoop input 32 (sourceInitial (fieldScalar input))

theorem exact_commonware_initial_state_derives_the_same_mathematical_invariants
    (input : CanonicalScalar) (nonzero : sourceFieldValue input ≠ 0) :
    sourceInitial input = stateMeaning (sourceSqrtInitial input) := by
  have root : sourceFieldValue (sourceSqrtInitial input).x =
      sourceFieldValue input ^ packWords sourceCommonwareExponent.toList := by
    simp only [sourceSqrtInitial,source_field_multiply_has_exact_ring_value,
      source_field_initial_power_has_exact_exponent,
      exact_commonware_exponent_is_the_successor_of_the_ff_initial_power,pow_succ]
  have residue : sourceFieldValue (sourceSqrtInitial input).x ^ 2 * (sourceFieldValue input)⁻¹ =
      sourceFieldValue (sourceSqrtInitial input).b := by
    rw [source_sqrt_initial_candidate_square_equals_input_times_initial_residue]
    calc
      _ = sourceFieldValue (sourceSqrtInitial input).b * (sourceFieldValue input * (sourceFieldValue input)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ nonzero,mul_one]
  simp only [sourceInitial,stateMeaning,← root,← pow_two,residue,
    exact_commonware_root_literal_has_the_qualified_field_value]
  rfl

theorem every_nonzero_square_derives_the_actual_commonware_initial_good_state
    (input : CanonicalScalar) (nonzero : sourceFieldValue input ≠ 0)
    (square : IsSquare (sourceFieldValue input)) : Good (sourceFieldValue input) (sourceInitial input) := by
  rw [exact_commonware_initial_state_derives_the_same_mathematical_invariants input nonzero]
  refine ⟨by change 1 ≤ 32; decide,?_,?_,?_,?_⟩
  · exact source_sqrt_initial_candidate_square_equals_input_times_initial_residue input
  · exact every_nonzero_square_input_derives_the_initial_half_order_bound input nonzero square
  · exact source_root_of_unity_has_exact_power_and_half_power.1
  · exact source_root_of_unity_has_exact_power_and_half_power.2

theorem actual_commonware_source_field_sqrt_is_sound (input returned : ZMod nullifierModulus)
    (success : sourceCommonwareFieldSqrt input = some returned) : returned*returned = input := by
  by_cases zero : input = 0
  · have same : (0 : ZMod nullifierModulus) = returned := by
      simpa only [sourceCommonwareFieldSqrt,if_pos zero,Option.some.injEq] using success
    simp only [← same,zero,mul_zero]
  · apply every_commonware_loop_success_has_the_checked_root input 32 (sourceInitial (fieldScalar input)) returned
    simpa only [sourceCommonwareFieldSqrt,if_neg zero] using success

theorem actual_commonware_source_field_sqrt_is_complete (input : ZMod nullifierModulus)
    (square : IsSquare input) : ∃ returned, sourceCommonwareFieldSqrt input = some returned := by
  by_cases zero : input = 0
  · exact ⟨0,by simp only [sourceCommonwareFieldSqrt,if_pos zero]⟩
  · have inputMeaning := actual_source_word_constructor_projects_to_every_field_input input
    have nonzero : sourceFieldValue (fieldScalar input) ≠ 0 := by simpa only [inputMeaning] using zero
    have derivedSquare : IsSquare (sourceFieldValue (fieldScalar input)) := by simpa only [inputMeaning] using square
    have good := every_nonzero_square_derives_the_actual_commonware_initial_good_state (fieldScalar input) nonzero derivedSquare
    rw [inputMeaning] at good
    obtain ⟨returned,success⟩ := actual_commonware_loop_is_complete_from_derived_good_invariants input 32
      (sourceInitial (fieldScalar input)) good (by change 32 ≤ 32; decide)
    exact ⟨returned,by simpa only [sourceCommonwareFieldSqrt,if_neg zero] using success⟩

theorem actual_commonware_source_field_sqrt_has_the_total_square_contract (input : ZMod nullifierModulus) :
    (sourceCommonwareFieldSqrt input).isSome = true ↔ IsSquare input := by
  constructor
  · intro present
    cases observed : sourceCommonwareFieldSqrt input with
    | none => simp only [observed,Option.isSome_none,Bool.false_eq_true] at present
    | some root => exact ⟨root,(actual_commonware_source_field_sqrt_is_sound input root observed).symm⟩
  · intro square
    obtain ⟨returned,success⟩ := actual_commonware_source_field_sqrt_is_complete input square
    simp only [success,Option.isSome_some]

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceCommonwareExponent
#print axioms sourceCommonwareExponent
set_option pp.all true in
#check @sourceCommonwareRoot
#print axioms sourceCommonwareRoot
set_option pp.all true in
#check @exact_commonware_exponent_is_the_successor_of_the_ff_initial_power
#print axioms exact_commonware_exponent_is_the_successor_of_the_ff_initial_power
set_option pp.all true in
#check @exact_commonware_root_literal_has_the_qualified_field_value
#print axioms exact_commonware_root_literal_has_the_qualified_field_value
set_option pp.all true in
#check @sourceInitial
#print axioms sourceInitial
set_option pp.all true in
#check @sourceCommonwareFieldSqrt
#print axioms sourceCommonwareFieldSqrt
set_option pp.all true in
#check @exact_commonware_initial_state_derives_the_same_mathematical_invariants
#print axioms exact_commonware_initial_state_derives_the_same_mathematical_invariants
set_option pp.all true in
#check @every_nonzero_square_derives_the_actual_commonware_initial_good_state
#print axioms every_nonzero_square_derives_the_actual_commonware_initial_good_state
set_option pp.all true in
#check @actual_commonware_source_field_sqrt_is_sound
#print axioms actual_commonware_source_field_sqrt_is_sound
set_option pp.all true in
#check @actual_commonware_source_field_sqrt_is_complete
#print axioms actual_commonware_source_field_sqrt_is_complete
set_option pp.all true in
#check @actual_commonware_source_field_sqrt_has_the_total_square_contract
#print axioms actual_commonware_source_field_sqrt_has_the_total_square_contract
end ShielddSecurity.TransferCommonwareSqrtComplete01
