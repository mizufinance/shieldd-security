import ShielddSecurity.TransferScalarExtendedSemantics01
import ShielddSecurity.TransferScalarConstantEquality01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPredicates01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferScalarPowInvariant01 (sourceZero)
open TransferScalarConstantEquality01 (sourceScalarWordsCtEqByte)
/-! Source-shaped scalar predicates and locked Choice-to-bool conversion.
Equality and zero are raw-word comparisons; canonical representation derives
their mathematical meaning. PrimeField::is_odd masks the first serialized
byte; its exact field parity and Choice validity are derived for all fields.
General bool conversion requires the documented valid Choice byte contract,
and the two modeled producers derive it. The head default is unreachable
for the proved32-byte serializer. Compiler/volatile barrier/native indexing/
ABI/private caller origins/timing/full Transfer remain separate interfaces. -/

def sourceChoiceBool (byte : UInt8) : Bool := decide (byte ≠ 0)

theorem valid_choice_source_boolean_conversion_is_exact_stored_byte_one
    (byte : UInt8) (valid : byte.toNat < 2) : sourceChoiceBool byte = true ↔ byte = 1 := by
  rw [sourceChoiceBool, decide_eq_true_eq]
  constructor
  · intro nonzero
    have notZero : byte.toNat ≠ 0 := by
      intro zero
      exact nonzero (UInt8.toNat_inj.mp zero)
    have one : byte.toNat = 1 := by omega
    exact UInt8.toNat_inj.mp one
  · intro one
    rw [one]
    decide

def sourceScalarEqualityBool (left right : CanonicalScalar) : Bool :=
  sourceChoiceBool (sourceScalarWordsCtEqByte left.words right.words)

theorem source_scalar_equality_boolean_has_exact_mathematical_field_meaning (left right : CanonicalScalar) :
    sourceScalarEqualityBool left right = true ↔ montgomeryValue left.words = montgomeryValue right.words := by
  have corresponds := TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal left right
  rw [sourceScalarEqualityBool,
    TransferScalarConstantEquality01.exact_source_scalar_equality_byte_derives_exact_raw_word_equality]
  by_cases same : left.words = right.words
  · rw [if_pos same]
    constructor
    · intro _; exact corresponds.mpr same
    · intro _; rfl
  · rw [if_neg same]
    constructor
    · intro impossible
      change false = true at impossible
      cases impossible
    · intro equal; exact False.elim (same (corresponds.mp equal))

theorem source_scalar_equality_choice_byte_has_derived_bit_invariant (left right : Vector UInt64 4) :
    (sourceScalarWordsCtEqByte left right).toNat < 2 := by
  rw [TransferScalarConstantEquality01.exact_source_scalar_equality_byte_derives_exact_raw_word_equality]
  split <;> decide

def sourceScalarZeroVartimeBool (scalar : CanonicalScalar) : Bool :=
  decide (scalar.words = sourceZero.words)

theorem source_scalar_vartime_zero_boolean_has_exact_mathematical_field_meaning (scalar : CanonicalScalar) :
    sourceScalarZeroVartimeBool scalar = true ↔ montgomeryValue scalar.words = 0 := by
  rw [sourceScalarZeroVartimeBool, decide_eq_true_eq]
  have corresponds := TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal scalar sourceZero
  rw [TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.1] at corresponds
  exact corresponds.symm

theorem first_typed_byte_low_bit_is_exact_little_endian_integer_parity (bytes : List UInt8) :
    (bytes.headD 0 &&& 1).toNat = decodeLE bytes % 2 := by
  cases bytes with
  | nil => rfl
  | cons byte rest =>
    rw [List.headD_cons, UInt8.toNat_and, UInt8.toNat_one, Nat.and_one_is_mod]
    change byte.toNat % 2 = (byte.toNat + 256 * decodeLE rest) % 2
    rw [Nat.add_mod, Nat.mul_mod]
    have even : ((256 % 2) * (decodeLE rest % 2)) % 2 = 0 := by
      change (0 * (decodeLE rest % 2)) % 2 = 0
      rw [Nat.zero_mul]
      rfl
    rw [even, Nat.add_zero, Nat.mod_mod]

def sourceScalarOddByte (scalar : CanonicalScalar) : UInt8 :=
  (serializerBytes scalar.words.toList).headD 0 &&& 1

theorem source_scalar_odd_choice_byte_has_exact_mathematical_field_parity (scalar : CanonicalScalar) :
    (sourceScalarOddByte scalar).toNat = montgomeryValue scalar.words % 2 := by
  rw [sourceScalarOddByte, first_typed_byte_low_bit_is_exact_little_endian_integer_parity]
  change TransferScalarLittleEndianBytes01.scalarKey scalar.words % 2 = _
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]

theorem source_scalar_odd_choice_byte_has_derived_bit_invariant (scalar : CanonicalScalar) :
    (sourceScalarOddByte scalar).toNat < 2 := by
  rw [source_scalar_odd_choice_byte_has_exact_mathematical_field_parity]
  exact Nat.mod_lt _ (by decide)

def sourceScalarOddBool (scalar : CanonicalScalar) : Bool := sourceChoiceBool (sourceScalarOddByte scalar)

theorem source_scalar_odd_boolean_has_exact_mathematical_field_parity (scalar : CanonicalScalar) :
    sourceScalarOddBool scalar = true ↔ montgomeryValue scalar.words % 2 = 1 := by
  rw [sourceScalarOddBool, valid_choice_source_boolean_conversion_is_exact_stored_byte_one _
    (source_scalar_odd_choice_byte_has_derived_bit_invariant scalar)]
  constructor
  · intro one
    have value := congrArg UInt8.toNat one
    rw [source_scalar_odd_choice_byte_has_exact_mathematical_field_parity] at value
    exact value
  · intro one
    apply UInt8.toNat_inj.mp
    rw [source_scalar_odd_choice_byte_has_exact_mathematical_field_parity, one]
    rfl

set_option pp.all true in
#check @sourceChoiceBool
#print axioms sourceChoiceBool
set_option pp.all true in
#check @valid_choice_source_boolean_conversion_is_exact_stored_byte_one
#print axioms valid_choice_source_boolean_conversion_is_exact_stored_byte_one
set_option pp.all true in
#check @sourceScalarEqualityBool
#print axioms sourceScalarEqualityBool
set_option pp.all true in
#check @source_scalar_equality_boolean_has_exact_mathematical_field_meaning
#print axioms source_scalar_equality_boolean_has_exact_mathematical_field_meaning
set_option pp.all true in
#check @source_scalar_equality_choice_byte_has_derived_bit_invariant
#print axioms source_scalar_equality_choice_byte_has_derived_bit_invariant
set_option pp.all true in
#check @sourceScalarZeroVartimeBool
#print axioms sourceScalarZeroVartimeBool
set_option pp.all true in
#check @source_scalar_vartime_zero_boolean_has_exact_mathematical_field_meaning
#print axioms source_scalar_vartime_zero_boolean_has_exact_mathematical_field_meaning
set_option pp.all true in
#check @first_typed_byte_low_bit_is_exact_little_endian_integer_parity
#print axioms first_typed_byte_low_bit_is_exact_little_endian_integer_parity
set_option pp.all true in
#check @sourceScalarOddByte
#print axioms sourceScalarOddByte
set_option pp.all true in
#check @source_scalar_odd_choice_byte_has_exact_mathematical_field_parity
#print axioms source_scalar_odd_choice_byte_has_exact_mathematical_field_parity
set_option pp.all true in
#check @source_scalar_odd_choice_byte_has_derived_bit_invariant
#print axioms source_scalar_odd_choice_byte_has_derived_bit_invariant
set_option pp.all true in
#check @sourceScalarOddBool
#print axioms sourceScalarOddBool
set_option pp.all true in
#check @source_scalar_odd_boolean_has_exact_mathematical_field_parity
#print axioms source_scalar_odd_boolean_has_exact_mathematical_field_parity
end ShielddSecurity.TransferScalarPredicates01
