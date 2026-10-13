import ShielddSecurity.TransferScalarInputSemantics01
import ShielddSecurity.TransferScalarPowField01
import ShielddSecurity.TransferScalarInvertField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarExtendedSemantics01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarExtendedFamily01 (ScalarExtendedProgram sourceExtendedEval)
open TransferScalarPublicConstants01 (PublicConstant sourceConstant)
open TransferScalarInputSemantics01
open TransferScalarAdditiveField01 (sourceCanonicalAdd sourceCanonicalSub sourceCanonicalNeg)
open TransferScalarPowInvariant01 (sourceZero sourceOne sourceCanonicalMul sourceCanonicalSquare sourcePow sourcePowVartime)
open TransferScalarInvertChain01 (sourceInvert sourceInvertPayload)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (decodeLE)
/-! Independent mathematical semantics of the complete represented extended
source evaluator: constants, integer and random-byte construction, arithmetic,
optimized square, both exponent loops, inversion refusal and eager Boolean
selection. Constants use a separate integer table checked by the kernel.
The inverse payload is obtained from the well-formed source chain, without
a desired output premise. This covers returned values and failure projection;
RNG distribution, eager side effects, compiler/ABI/native caller census and
full Transfer correspondence remain separate obligations. -/

def mathematicalPublicConstant : PublicConstant → Nat
  | .twoInverse => (nullifierModulus + 1) / 2
  | .generator => 7
  | .rootOfUnity => 10238227357739495823651030575849232062558860180284477541189508159991286009131
  | .rootOfUnityInverse => 2361660012179324004544952053205906600198439069793331036989202475535180077688
  | .delta => 3793952369011177517951424454785176000433849974408744014172535497121832470999

theorem every_source_public_constant_has_the_independently_stated_integer_value (constant : PublicConstant) :
    montgomeryValue (sourceConstant constant).words = mathematicalPublicConstant constant := by
  cases constant <;> decide

theorem source_inversion_has_exact_mathematical_power_and_zero_refusal_semantics (scalar : CanonicalScalar) :
    (sourceInvert scalar).map (fun value : CanonicalScalar => montgomeryValue value.words) =
      if montgomeryValue scalar.words = 0 then none
      else some (montgomeryValue scalar.words ^ (nullifierModulus - 2) % nullifierModulus) := by
  have zero := TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal scalar sourceZero
  rw [TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.1] at zero
  by_cases isZero : scalar.words = sourceZero.words
  · rw [sourceInvert, if_pos isZero, if_pos (zero.mpr isZero)]
    rfl
  · have nonzero : montgomeryValue scalar.words ≠ 0 := fun impossible => isZero (zero.mp impossible)
    obtain ⟨payload, returned⟩ := TransferScalarInvertChain01.exact_source_invert_chain_derives_successful_canonical_payload scalar
    rw [sourceInvert, if_neg isZero, if_neg nonzero, returned]
    exact congrArg Option.some (TransferScalarInvertField01.exact_source_invert_payload_has_modulus_minus_two_field_power scalar payload returned)

theorem source_u64_constructor_has_exact_integer_field_semantics (value : UInt64) :
    (sourceExtendedEval (.fromU64 value)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = some value.toNat := by
  change (TransferScalarInputFamily01.sourceInputEval (.raw #v[value, 0, 0, 0])).map
    (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
  rw [raw_source_input_constructor_has_derived_integer_residue_semantics]
  have packed : packWords (#v[value, 0, 0, 0] : Vector UInt64 4).toList = value.toNat := by
    change value.toNat + 18446744073709551616 * (0 + 18446744073709551616 *
      (0 + 18446744073709551616 * (0 + 18446744073709551616 * 0))) = value.toNat
    simp only [Nat.mul_zero, Nat.add_zero]
  rw [packed, Nat.mod_eq_of_lt (Nat.lt_trans value.toNat_lt (by decide : UInt64.size < nullifierModulus))]

theorem mapped_canonical_option_partial_operation_preserves_derived_field_and_refusal_semantics
    (value : Option CanonicalScalar) (sourceOp : CanonicalScalar → Option CanonicalScalar) (mathOp : Nat → Option Nat)
    (corresponds : ∀ a, (sourceOp a).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = mathOp (montgomeryValue a.words)) :
    (value.bind sourceOp).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) =
      (value.map (fun scalar : CanonicalScalar => montgomeryValue scalar.words)).bind mathOp := by
  cases value with
  | none => rfl
  | some a => exact corresponds a

def mathematicalExtendedEval : ScalarExtendedProgram → Option Nat
  | .input program => mathematicalInputEval program
  | .constant value => some (mathematicalPublicConstant value)
  | .zero => some 0
  | .one => some 1
  | .fromU64 value => some value.toNat
  | .randomBytes bytes => some (decodeLE bytes.toList % nullifierModulus)
  | .add left right => do
    let a ← mathematicalExtendedEval left; let b ← mathematicalExtendedEval right
    pure ((a + b) % nullifierModulus)
  | .sub left right => do
    let a ← mathematicalExtendedEval left; let b ← mathematicalExtendedEval right
    pure ((a + nullifierModulus - b) % nullifierModulus)
  | .mul left right => do
    let a ← mathematicalExtendedEval left; let b ← mathematicalExtendedEval right
    pure ((a * b) % nullifierModulus)
  | .neg value => do
    let a ← mathematicalExtendedEval value; pure ((nullifierModulus - a) % nullifierModulus)
  | .double value => do
    let a ← mathematicalExtendedEval value; pure ((a + a) % nullifierModulus)
  | .square value => do
    let a ← mathematicalExtendedEval value; pure ((a * a) % nullifierModulus)
  | .pow value exponent => do
    let a ← mathematicalExtendedEval value; pure (a ^ packWords exponent.toList % nullifierModulus)
  | .powVartime value exponent => do
    let a ← mathematicalExtendedEval value; pure (a ^ packWords exponent.toList % nullifierModulus)
  | .invert value => do
    let a ← mathematicalExtendedEval value
    if a = 0 then none else some (a ^ (nullifierModulus - 2) % nullifierModulus)
  | .select choice first second => do
    let a ← mathematicalExtendedEval first; let b ← mathematicalExtendedEval second
    pure (if choice then b else a)

theorem entire_represented_extended_source_evaluator_has_exact_independent_field_and_refusal_semantics
    (program : ScalarExtendedProgram) :
    (sourceExtendedEval program).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = mathematicalExtendedEval program := by
  induction program with
  | input program => exact entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics program
  | constant value => exact congrArg Option.some (every_source_public_constant_has_the_independently_stated_integer_value value)
  | zero => exact congrArg Option.some TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.1
  | one => exact congrArg Option.some TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.2
  | fromU64 value => exact source_u64_constructor_has_exact_integer_field_semantics value
  | randomBytes bytes => exact wide_source_input_constructor_has_derived_integer_residue_semantics bytes
  | add left right leftIH rightIH =>
    change (do let a ← sourceExtendedEval left; let b ← sourceExtendedEval right; pure (sourceCanonicalAdd a b)).map
      (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ sourceCanonicalAdd (fun x y => (x + y) % nullifierModulus)
      TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum, leftIH, rightIH]
    rfl
  | sub left right leftIH rightIH =>
    change (do let a ← sourceExtendedEval left; let b ← sourceExtendedEval right; pure (sourceCanonicalSub a b)).map
      (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ sourceCanonicalSub (fun x y => (x + nullifierModulus - y) % nullifierModulus)
      TransferScalarAdditiveField01.actual_source_canonical_sub_has_exact_mathematical_field_difference, leftIH, rightIH]
    rfl
  | mul left right leftIH rightIH =>
    change (do let a ← sourceExtendedEval left; let b ← sourceExtendedEval right; pure (sourceCanonicalMul a b)).map
      (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ sourceCanonicalMul (fun x y => (x * y) % nullifierModulus)
      TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value, leftIH, rightIH]
    rfl
  | neg value ih =>
    change (do let a ← sourceExtendedEval value; pure (sourceCanonicalNeg a)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ sourceCanonicalNeg (fun x => (nullifierModulus - x) % nullifierModulus)
      TransferScalarAdditiveField01.actual_source_canonical_negation_has_exact_mathematical_field_value, ih]
    rfl
  | double value ih =>
    change (do let a ← sourceExtendedEval value; pure (sourceCanonicalAdd a a)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ (fun a => sourceCanonicalAdd a a) (fun x => (x + x) % nullifierModulus)
      (fun a => TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum a a), ih]
    rfl
  | square value ih =>
    change (do let a ← sourceExtendedEval value; pure (sourceCanonicalSquare a)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ sourceCanonicalSquare (fun x => (x * x) % nullifierModulus)
      TransferScalarFieldValues01.actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value, ih]
    rfl
  | pow value exponent ih =>
    change (do let a ← sourceExtendedEval value; pure (sourcePow a exponent)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ (fun a => sourcePow a exponent) (fun x => x ^ packWords exponent.toList % nullifierModulus)
      (fun a => TransferScalarPowField01.exact_source_constant_time_pow_has_mathematical_little_endian_field_power a exponent), ih]
    rfl
  | powVartime value exponent ih =>
    change (do let a ← sourceExtendedEval value; pure (sourcePowVartime a exponent)).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ (fun a => sourcePowVartime a exponent) (fun x => x ^ packWords exponent.toList % nullifierModulus)
      (fun a => TransferScalarPowField01.exact_source_variable_time_pow_has_mathematical_little_endian_field_power a exponent), ih]
    rfl
  | invert value ih =>
    change ((sourceExtendedEval value).bind sourceInvert).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_partial_operation_preserves_derived_field_and_refusal_semantics _ sourceInvert
      (fun x => if x = 0 then none else some (x ^ (nullifierModulus - 2) % nullifierModulus))
      source_inversion_has_exact_mathematical_power_and_zero_refusal_semantics, ih]
    rfl
  | select choice first second firstIH secondIH =>
    change (do let a ← sourceExtendedEval first; let b ← sourceExtendedEval second; pure (if choice then b else a)).map
      (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ (fun a b => if choice then b else a) (fun x y => if choice then y else x)
      (by intro a b; cases choice <;> rfl), firstIH, secondIH]
    rfl

set_option pp.all true in
#check @mathematicalPublicConstant
#print axioms mathematicalPublicConstant
set_option pp.all true in
#check @every_source_public_constant_has_the_independently_stated_integer_value
#print axioms every_source_public_constant_has_the_independently_stated_integer_value
set_option pp.all true in
#check @source_inversion_has_exact_mathematical_power_and_zero_refusal_semantics
#print axioms source_inversion_has_exact_mathematical_power_and_zero_refusal_semantics
set_option pp.all true in
#check @source_u64_constructor_has_exact_integer_field_semantics
#print axioms source_u64_constructor_has_exact_integer_field_semantics
set_option pp.all true in
#check @mapped_canonical_option_partial_operation_preserves_derived_field_and_refusal_semantics
#print axioms mapped_canonical_option_partial_operation_preserves_derived_field_and_refusal_semantics
set_option pp.all true in
#check @mathematicalExtendedEval
#print axioms mathematicalExtendedEval
set_option pp.all true in
#check @entire_represented_extended_source_evaluator_has_exact_independent_field_and_refusal_semantics
#print axioms entire_represented_extended_source_evaluator_has_exact_independent_field_and_refusal_semantics
end ShielddSecurity.TransferScalarExtendedSemantics01
