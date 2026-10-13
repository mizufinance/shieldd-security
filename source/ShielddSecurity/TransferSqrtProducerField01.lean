import ShielddSecurity.TransferSqrtProducerLoop01
import ShielddSecurity.TransferScalarInverseCorrectness01
import ShielddSecurity.ModularPower
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSqrtProducerField01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarPowInvariant01 (sourceCanonicalMul sourceCanonicalSquare sourcePowVartime)
open TransferScalarChoiceMasks01 (SourceChoiceByte sourceMaskedScalarSelect)
open TransferScalarPublicConstants01 (sourceConstant)
open TransferSqrtProducerLoop01
/-! Interpretation of the qualified ff producer's actual word operations in
the exact prime ZMod field. Closed root-order checks use logarithmic modular
power; symbolic recurrences replace full loop evaluation. Initial square-input
order and zero-input propagation are derived, not caller output assumptions.
Nonzero Tonelli-Shanks progress/completeness and native correspondence remain
separate obligations. -/

def sourceFieldValue (value : CanonicalScalar) : ZMod nullifierModulus :=
  (montgomeryValue value.words : ZMod nullifierModulus)

theorem source_field_multiply_has_exact_ring_value (a b : CanonicalScalar) :
    sourceFieldValue (sourceCanonicalMul a b) = sourceFieldValue a * sourceFieldValue b := by
  unfold sourceFieldValue
  rw [TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value]
  simp only [ZMod.natCast_mod, Nat.cast_mul]

theorem source_field_square_has_exact_ring_value (a : CanonicalScalar) :
    sourceFieldValue (sourceCanonicalSquare a) = sourceFieldValue a ^ 2 := by
  unfold sourceFieldValue
  rw [TransferScalarFieldValues01.actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value]
  simp only [ZMod.natCast_mod, Nat.cast_mul, pow_two]

theorem source_field_masked_selection_has_exact_branch (a b : CanonicalScalar) (choice : SourceChoiceByte) :
    sourceFieldValue (sourceMaskedScalarSelect a b choice) =
      if choice.byte = 0 then sourceFieldValue a else sourceFieldValue b := by
  rw [TransferScalarChoiceMasks01.exact_source_masked_scalar_selection_equals_the_whole_canonical_branch]
  split <;> rfl

theorem source_field_initial_power_has_exact_exponent (input : CanonicalScalar) :
    sourceFieldValue (sourcePowVartime input sourceSqrtExponent) =
      sourceFieldValue input ^ (((nullifierModulus - 1) / 2 ^ 32 - 1) / 2) := by
  unfold sourceFieldValue
  rw [source_sqrt_initial_power_has_exact_mathematical_exponent]
  simp only [ZMod.natCast_mod, Nat.cast_pow]

theorem source_root_of_unity_has_exact_power_and_half_power :
    sourceFieldValue (sourceConstant .rootOfUnity) ^ (2 ^ 32) = 1 ∧
      sourceFieldValue (sourceConstant .rootOfUnity) ^ (2 ^ 31) = -1 := by
  constructor
  · exact ModularPower.power_eq_one nullifierModulus
      (montgomeryValue (sourceConstant .rootOfUnity).words) (2 ^ 32) (by decide +kernel)
  · rw [sourceFieldValue, ← ModularPower.power_sound]
    have checked : ModularPower.power nullifierModulus
        (montgomeryValue (sourceConstant .rootOfUnity).words) (2 ^ 31) = nullifierModulus - 1 := by decide +kernel
    rw [checked, Nat.cast_sub (by decide : 1 ≤ nullifierModulus), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem source_sqrt_initial_candidate_square_equals_input_times_initial_residue (input : CanonicalScalar) :
    sourceFieldValue (sourceSqrtInitial input).x ^ 2 =
      sourceFieldValue input * sourceFieldValue (sourceSqrtInitial input).b := by
  simp only [sourceSqrtInitial, source_field_multiply_has_exact_ring_value]
  ring

theorem source_sqrt_initial_residue_has_exact_odd_power (input : CanonicalScalar) :
    sourceFieldValue (sourceSqrtInitial input).b =
      sourceFieldValue input ^ ((nullifierModulus - 1) / 2 ^ 32) := by
  simp only [sourceSqrtInitial, source_field_multiply_has_exact_ring_value, source_field_initial_power_has_exact_exponent]
  have count : ((nullifierModulus - 1) / 2 ^ 32 - 1) / 2 * 2 + 1 =
      (nullifierModulus - 1) / 2 ^ 32 := by decide
  calc
    _ = sourceFieldValue input ^ ((((nullifierModulus - 1) / 2 ^ 32 - 1) / 2) * 2 + 1) := by
      rw [pow_add, pow_mul, pow_two, pow_one]
      ring
    _ = _ := congrArg (fun n : Nat => sourceFieldValue input ^ n) count

theorem every_nonzero_square_input_derives_the_initial_half_order_bound
    (input : CanonicalScalar) (nonzero : sourceFieldValue input ≠ 0)
    (square : IsSquare (sourceFieldValue input)) :
    sourceFieldValue (sourceSqrtInitial input).b ^ (2 ^ 31) = 1 := by
  letI : Fact (Nat.Prime nullifierModulus) := ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
  letI : NeZero nullifierModulus := ⟨by decide⟩
  obtain ⟨root,rootEquation⟩ := square
  have rootNonzero : root ≠ 0 := by
    intro zero
    exact nonzero (by simpa only [zero,mul_zero] using rootEquation)
  let unit : (ZMod nullifierModulus)ˣ := Units.mk0 root rootNonzero
  have cardinality : Fintype.card (ZMod nullifierModulus)ˣ = nullifierModulus - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have unitPower : unit ^ (nullifierModulus - 1) = 1 := by
    rw [← cardinality]
    exact pow_card_eq_one
  have fermat := congrArg (fun u : (ZMod nullifierModulus)ˣ => (u : ZMod nullifierModulus)) unitPower
  change root ^ (nullifierModulus - 1) = 1 at fermat
  rw [source_sqrt_initial_residue_has_exact_odd_power, rootEquation, ← pow_two, ← pow_mul, ← pow_mul]
  have count : 2 * (((nullifierModulus - 1) / 2 ^ 32) * (2 ^ 31)) = nullifierModulus - 1 := by decide +kernel
  rw [count]
  exact fermat

theorem every_source_sqrt_round_preserves_a_zero_candidate
    (state : SqrtState) (maxV : Nat) (zero : sourceFieldValue state.x = 0) :
    sourceFieldValue (sourceSqrtRound state maxV).x = 0 := by
  unfold sourceSqrtRound
  dsimp only
  rw [source_field_masked_selection_has_exact_branch, source_field_multiply_has_exact_ring_value, zero]
  split <;> simp only [zero_mul]

theorem every_symbolic_source_sqrt_round_walk_preserves_a_zero_candidate
    (rounds : List Nat) (state : SqrtState) (zero : sourceFieldValue state.x = 0) :
    sourceFieldValue (rounds.foldl sourceSqrtRound state).x = 0 := by
  induction rounds generalizing state with
  | nil => exact zero
  | cons maxV rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (every_source_sqrt_round_preserves_a_zero_candidate _ _ zero)

theorem source_sqrt_of_mathematical_zero_derives_a_zero_loop_payload
    (input : CanonicalScalar) (zero : sourceFieldValue input = 0) :
    sourceFieldValue (sourceSqrtPayload input) = 0 := by
  have initial : sourceFieldValue (sourceSqrtInitial input).x = 0 := by
    simp only [sourceSqrtInitial, source_field_multiply_has_exact_ring_value, zero, mul_zero]
  exact every_symbolic_source_sqrt_round_walk_preserves_a_zero_candidate _ _ initial

theorem source_field_value_equality_is_exact_word_equality (a b : CanonicalScalar) :
    sourceFieldValue a = sourceFieldValue b ↔ a.words = b.words := by
  have residues := ZMod.natCast_eq_natCast_iff' (montgomeryValue a.words) (montgomeryValue b.words) nullifierModulus
  have mathematical : sourceFieldValue a = sourceFieldValue b ↔ montgomeryValue a.words = montgomeryValue b.words := by
    simpa only [sourceFieldValue, montgomeryValue, Nat.mod_mod] using residues
  exact mathematical.trans (TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal a b)

theorem source_field_value_zero_is_exact_mathematical_zero (input : CanonicalScalar) :
    sourceFieldValue input = 0 ↔ montgomeryValue input.words = 0 := by
  have residues := ZMod.natCast_eq_natCast_iff' (montgomeryValue input.words) 0 nullifierModulus
  simpa only [sourceFieldValue, montgomeryValue, Nat.cast_zero, Nat.mod_mod, Nat.zero_mod] using residues

theorem source_sqrt_zero_input_returns_the_same_exact_canonical_zero
    (input : CanonicalScalar) (zero : sourceFieldValue input = 0) :
    sourceSqrt input = some input := by
  have payloadZero := source_sqrt_of_mathematical_zero_derives_a_zero_loop_payload input zero
  have sameWords := (source_field_value_equality_is_exact_word_equality (sourceSqrtPayload input) input).mp
    (payloadZero.trans zero.symm)
  have same := TransferScalarChoiceMasks01.canonical_scalar_objects_equal_of_exact_raw_word_equality _ _ sameWords
  have root : (montgomeryValue (sourceSqrtPayload input).words * montgomeryValue (sourceSqrtPayload input).words) %
      nullifierModulus = montgomeryValue input.words := by
    rw [(source_field_value_zero_is_exact_mathematical_zero _).mp payloadZero,
      (source_field_value_zero_is_exact_mathematical_zero _).mp zero]
    rfl
  rw [source_sqrt_producer_returns_exactly_its_qualified_final_check,
    TransferScalarSqrtAcceptance01.sourceSqrtFinalOption,
    if_pos ((TransferScalarSqrtAcceptance01.source_sqrt_final_choice_accepts_exactly_the_mathematical_square _ _).mpr root), same]

set_option pp.all true in
#check @sourceFieldValue
#print axioms sourceFieldValue
set_option pp.all true in
#check @source_field_multiply_has_exact_ring_value
#print axioms source_field_multiply_has_exact_ring_value
set_option pp.all true in
#check @source_field_square_has_exact_ring_value
#print axioms source_field_square_has_exact_ring_value
set_option pp.all true in
#check @source_field_masked_selection_has_exact_branch
#print axioms source_field_masked_selection_has_exact_branch
set_option pp.all true in
#check @source_field_initial_power_has_exact_exponent
#print axioms source_field_initial_power_has_exact_exponent
set_option pp.all true in
#check @source_root_of_unity_has_exact_power_and_half_power
#print axioms source_root_of_unity_has_exact_power_and_half_power
set_option pp.all true in
#check @source_sqrt_initial_candidate_square_equals_input_times_initial_residue
#print axioms source_sqrt_initial_candidate_square_equals_input_times_initial_residue
set_option pp.all true in
#check @source_sqrt_initial_residue_has_exact_odd_power
#print axioms source_sqrt_initial_residue_has_exact_odd_power
set_option pp.all true in
#check @every_nonzero_square_input_derives_the_initial_half_order_bound
#print axioms every_nonzero_square_input_derives_the_initial_half_order_bound
set_option pp.all true in
#check @every_source_sqrt_round_preserves_a_zero_candidate
#print axioms every_source_sqrt_round_preserves_a_zero_candidate
set_option pp.all true in
#check @every_symbolic_source_sqrt_round_walk_preserves_a_zero_candidate
#print axioms every_symbolic_source_sqrt_round_walk_preserves_a_zero_candidate
set_option pp.all true in
#check @source_sqrt_of_mathematical_zero_derives_a_zero_loop_payload
#print axioms source_sqrt_of_mathematical_zero_derives_a_zero_loop_payload
set_option pp.all true in
#check @source_field_value_equality_is_exact_word_equality
#print axioms source_field_value_equality_is_exact_word_equality
set_option pp.all true in
#check @source_field_value_zero_is_exact_mathematical_zero
#print axioms source_field_value_zero_is_exact_mathematical_zero
set_option pp.all true in
#check @source_sqrt_zero_input_returns_the_same_exact_canonical_zero
#print axioms source_sqrt_zero_input_returns_the_same_exact_canonical_zero
end ShielddSecurity.TransferSqrtProducerField01
