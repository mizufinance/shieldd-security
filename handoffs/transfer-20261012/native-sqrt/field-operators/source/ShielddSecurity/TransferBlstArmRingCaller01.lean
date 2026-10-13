import ShielddSecurity.TransferBlstArmFieldCodec01
import ShielddSecurity.TransferCommonwareExpField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmRingCaller01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmCiosWalk01 (sourceCiosProduct)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceCiosProduct sourceBlstFrWordMeaning montgomeryValue
  TransferScalarPowInvariant01.sourceCanonicalSquare

/-! Commonware Scalar inherits Multiplicative::square, which clones the input
and calls MulAssign, i.e. blst_fr_mul. It does not call blst_fr_sqr.
The actual source monoid-exp bit recurrence is instantiated with the complete
CIOS source word operation and the original BLST_FR_ONE words. Canonical result
domains and field values are derived by that operation, not supplied per step.
Native Clone/in-place pointers, compiler/ISA and blst_fr_inverse remain separate.
This does not infer a native inverse or the complete native sqrt result. -/

def sourceArmMul (left right : CanonicalScalar) : CanonicalScalar :=
  sourceCiosProduct left right.words

theorem source_caller_multiply_derives_the_two_original_field_values_product
    (left right : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceArmMul left right).words =
      sourceBlstFrWordMeaning left.words * sourceBlstFrWordMeaning right.words := by
  exact TransferBlstArmCiosWalk01.actual_original_cios_program_derives_the_two_original_input_field_values_product left right.words

def sourceCallerSquare (value : CanonicalScalar) : CanonicalScalar := sourceArmMul value value

theorem original_default_square_caller_derives_the_original_input_field_square (value : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceCallerSquare value).words = (sourceBlstFrWordMeaning value.words)^2 := by
  rw [sourceCallerSquare,source_caller_multiply_derives_the_two_original_field_values_product,pow_two]

theorem canonical_original_word_field_meaning_is_injective (left right : CanonicalScalar)
    (same : sourceBlstFrWordMeaning left.words = sourceBlstFrWordMeaning right.words) : left = right := by
  apply TransferCanonicalSourceMembership01.canonical_source_key_is_injective_on_entire_typed_fields
  change TransferScalarLittleEndianBytes01.scalarKey left.words = TransferScalarLittleEndianBytes01.scalarKey right.words
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  have leftBound : montgomeryValue left.words < nullifierModulus := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical left.words
  have rightBound : montgomeryValue right.words < nullifierModulus := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical right.words
  have values := congrArg (fun value : ZMod nullifierModulus => value.val) same
  simpa only [sourceBlstFrWordMeaning,ZMod.val_natCast,Nat.mod_eq_of_lt leftBound,Nat.mod_eq_of_lt rightBound] using values

theorem original_default_square_caller_and_sdk_optimized_square_retain_the_same_entire_field (value : CanonicalScalar) :
    sourceCallerSquare value = TransferScalarPowInvariant01.sourceCanonicalSquare value := by
  apply canonical_original_word_field_meaning_is_injective
  rw [original_default_square_caller_derives_the_original_input_field_square,pow_two]
  symm
  simp only [sourceBlstFrWordMeaning,
    TransferScalarFieldValues01.actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value,
    ZMod.natCast_mod,Nat.cast_mul]

def sourceCallerOne : CanonicalScalar :=
  ⟨#v[0x00000001fffffffe,0x5884b7fa00034802,0x998c4fefecbc4ff5,0x1824b159acc5056f],by decide⟩

theorem original_blst_fr_one_words_have_exact_original_field_value :
    sourceBlstFrWordMeaning sourceCallerOne.words = 1 := by
  have numeric : montgomeryValue sourceCallerOne.words = 1 := by
    rw [montgomeryValue]
    decide
  rw [sourceBlstFrWordMeaning,numeric,Nat.cast_one]

def sourceCallerExpWalk : List Bool → CanonicalScalar → CanonicalScalar → CanonicalScalar
  | [],acc,_ => acc
  | bit :: rest,acc,base => sourceCallerExpWalk rest
      (if bit then sourceArmMul acc base else acc) (sourceCallerSquare base)

theorem symbolic_original_word_exp_walk_interprets_the_actual_generic_monoid_exp_recurrence
    (bits : List Bool) (acc base : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceCallerExpWalk bits acc base).words =
      TransferCommonwareExpField01.sourceMonoidExpWalk bits
        (sourceBlstFrWordMeaning acc.words) (sourceBlstFrWordMeaning base.words) := by
  induction bits generalizing acc base with
  | nil => rfl
  | cons bit rest ih =>
      rw [sourceCallerExpWalk,ih,TransferCommonwareExpField01.sourceMonoidExpWalk,
        original_default_square_caller_derives_the_original_input_field_square,pow_two]
      cases bit
      · rfl
      · change TransferCommonwareExpField01.sourceMonoidExpWalk rest
          (sourceBlstFrWordMeaning (sourceArmMul acc base).words)
          (sourceBlstFrWordMeaning base.words * sourceBlstFrWordMeaning base.words) =
          TransferCommonwareExpField01.sourceMonoidExpWalk rest
          (sourceBlstFrWordMeaning acc.words * sourceBlstFrWordMeaning base.words)
          (sourceBlstFrWordMeaning base.words * sourceBlstFrWordMeaning base.words)
        rw [source_caller_multiply_derives_the_two_original_field_values_product]

def sourceCallerSqrtSeed (value : CanonicalScalar) : CanonicalScalar :=
  sourceCallerExpWalk TransferCommonwareExpBits01.sourceSqrtExponentBits sourceCallerOne value

theorem original_word_multiply_square_and_bit_iterator_derive_the_actual_original_sqrt_seed_value
    (value : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceCallerSqrtSeed value).words =
      (sourceBlstFrWordMeaning value.words)^
        TransferScalarWordPrimitives01.packWords TransferCommonwareSqrtComplete01.sourceCommonwareExponent.toList := by
  rw [sourceCallerSqrtSeed,symbolic_original_word_exp_walk_interprets_the_actual_generic_monoid_exp_recurrence,
    original_blst_fr_one_words_have_exact_original_field_value,
    TransferCommonwareExpField01.actual_source_monoid_exp_walk_has_the_exact_little_endian_power,one_mul,
    TransferCommonwareExpBits01.exact_commonware_sqrt_bit_iterator_reconstructs_the_locked_exponent]
set_option pp.all true in
#check @sourceArmMul
#print axioms sourceArmMul
set_option pp.all true in
#check @source_caller_multiply_derives_the_two_original_field_values_product
#print axioms source_caller_multiply_derives_the_two_original_field_values_product
set_option pp.all true in
#check @sourceCallerSquare
#print axioms sourceCallerSquare
set_option pp.all true in
#check @original_default_square_caller_derives_the_original_input_field_square
#print axioms original_default_square_caller_derives_the_original_input_field_square
set_option pp.all true in
#check @canonical_original_word_field_meaning_is_injective
#print axioms canonical_original_word_field_meaning_is_injective
set_option pp.all true in
#check @original_default_square_caller_and_sdk_optimized_square_retain_the_same_entire_field
#print axioms original_default_square_caller_and_sdk_optimized_square_retain_the_same_entire_field
set_option pp.all true in
#check @sourceCallerOne
#print axioms sourceCallerOne
set_option pp.all true in
#check @original_blst_fr_one_words_have_exact_original_field_value
#print axioms original_blst_fr_one_words_have_exact_original_field_value
set_option pp.all true in
#check @sourceCallerExpWalk
#print axioms sourceCallerExpWalk
set_option pp.all true in
#check @symbolic_original_word_exp_walk_interprets_the_actual_generic_monoid_exp_recurrence
#print axioms symbolic_original_word_exp_walk_interprets_the_actual_generic_monoid_exp_recurrence
set_option pp.all true in
#check @sourceCallerSqrtSeed
#print axioms sourceCallerSqrtSeed
set_option pp.all true in
#check @original_word_multiply_square_and_bit_iterator_derive_the_actual_original_sqrt_seed_value
#print axioms original_word_multiply_square_and_bit_iterator_derive_the_actual_original_sqrt_seed_value
end ShielddSecurity.TransferBlstArmRingCaller01
