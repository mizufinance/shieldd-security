import ShielddSecurity.TransferCompleteBlockDriver01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalWordEquality01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (scalarKey serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic equal-width u64 packing injection and canonical internal-word
Montgomery bijection. Under explicit canonical internal raw representation,
raw vector equality iff mathematical scalar equality iff exact source bytes.
Canonical domain excludes raw aliases modulo p; arbitrary raw vectors are
not claimed to have injective scalar serialization. Native private Scalar
representation invariant/PartialEq/constant-time primitives/word selector/
byte/hash/Clone/collection correspondence remains explicit; no native credit. -/

structure CanonicalScalar where
  words : Vector UInt64 4
  canonical : packWords words.toList < nullifierModulus

theorem packed_word_cons_division_recovers_exact_tail (word : UInt64) (rest : List UInt64) :
    packWords (word :: rest) / radix64 = packWords rest := by
  have bounded : word.toNat < radix64 := word.toNat_lt
  change (word.toNat + radix64 * packWords rest) / radix64 = packWords rest
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt bounded, Nat.zero_add]

theorem equal_width_packed_u64_lists_are_equal (left right : List UInt64)
    (width : left.length = right.length) (packed : packWords left = packWords right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head rest => simp only [List.length_nil, List.length_cons] at width; omega
  | cons head rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have lengths : rest.length = tail.length := Nat.succ.inj width
      have heads := congrArg (fun value => value % radix64) packed
      simp only [TransferScalarMontgomeryValue01.packed_vector_modulo_radix_is_actual_low_word, List.headD_cons] at heads
      have headEq : head = other := UInt64.toNat_inj.mp heads
      have tails := congrArg (fun value => value / radix64) packed
      change packWords (head :: rest) / radix64 = packWords (other :: tail) / radix64 at tails
      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails
      exact (congrArg (fun word : UInt64 => word :: rest) headEq).trans (congrArg (List.cons other) (ih tail lengths tails))

theorem packed_fixed_word_vectors_equal_iff_raw_vectors_equal (left right : Vector UInt64 4) :
    packWords left.toList = packWords right.toList ↔ left = right := by
  constructor
  · intro same
    exact Vector.toList_inj.mp (equal_width_packed_u64_lists_are_equal left.toList right.toList (by simp only [Vector.length_toList]) same)
  · intro same
    exact congrArg (fun words : Vector UInt64 4 => packWords words.toList) same

theorem canonical_internal_math_values_equal_iff_raw_words_equal (left right : CanonicalScalar) :
    montgomeryValue left.words = montgomeryValue right.words ↔ left.words = right.words := by
  constructor
  · intro same
    have leftRelation := TransferScalarMontgomeryValue01.typed_source_serializer_preserves_four_round_montgomery_relation left.words.toList Vector.length_toList
    have rightRelation := TransferScalarMontgomeryValue01.typed_source_serializer_preserves_four_round_montgomery_relation right.words.toList Vector.length_toList
    change (radix64 ^ 4 * scalarKey left.words) % nullifierModulus = packWords left.words.toList % nullifierModulus at leftRelation
    change (radix64 ^ 4 * scalarKey right.words) % nullifierModulus = packWords right.words.toList % nullifierModulus at rightRelation
    rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value] at leftRelation rightRelation
    have packed := congrArg (fun value => radix64 ^ 4 * value % nullifierModulus) same
    change (radix64 ^ 4 * montgomeryValue left.words) % nullifierModulus = (radix64 ^ 4 * montgomeryValue right.words) % nullifierModulus at packed
    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed
    exact (packed_fixed_word_vectors_equal_iff_raw_vectors_equal left.words right.words).mp packed
  · intro same
    exact congrArg montgomeryValue same

theorem canonical_internal_source_bytes_equal_iff_raw_words_equal (left right : CanonicalScalar) :
    serializerBytes left.words.toList = serializerBytes right.words.toList ↔ left.words = right.words :=
  (TransferScalarByteEquality01.source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal left.words right.words).trans
    (canonical_internal_math_values_equal_iff_raw_words_equal left right)

set_option pp.all true in
#check @CanonicalScalar
#print axioms CanonicalScalar
set_option pp.all true in
#check @packed_word_cons_division_recovers_exact_tail
#print axioms packed_word_cons_division_recovers_exact_tail
set_option pp.all true in
#check @equal_width_packed_u64_lists_are_equal
#print axioms equal_width_packed_u64_lists_are_equal
set_option pp.all true in
#check @packed_fixed_word_vectors_equal_iff_raw_vectors_equal
#print axioms packed_fixed_word_vectors_equal_iff_raw_vectors_equal
set_option pp.all true in
#check @canonical_internal_math_values_equal_iff_raw_words_equal
#print axioms canonical_internal_math_values_equal_iff_raw_words_equal
set_option pp.all true in
#check @canonical_internal_source_bytes_equal_iff_raw_words_equal
#print axioms canonical_internal_source_bytes_equal_iff_raw_words_equal
end ShielddSecurity.TransferCanonicalWordEquality01
