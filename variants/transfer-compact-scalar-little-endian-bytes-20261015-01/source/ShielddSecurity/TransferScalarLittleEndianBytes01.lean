import ShielddSecurity.TransferScalarMaskedNormalization01
import Init.Data.Vector.Lemmas
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarLittleEndianBytes01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (nativeRounds)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic typed UInt8 little-endian codec and exact four-limb source-shaped
serialization. Finite UInt64 inputs supply word bounds; byte width/order,
numeric reconstruction and canonical field range are derived from the actual
carry/sub/add-back model. No byte-range or canonical-input bound is supplied.
Pinned Rust array/slice order is checked separately from to_le_bytes, native
trace, Scalar Montgomery semantic identity and typed runtime projection. -/
def encodeLE : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat (value % 256) :: encodeLE width (value / 256)
def decodeLE : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest
def wordBytes (word : UInt64) : List UInt8 := encodeLE 8 word.toNat
def wordsBytes : List UInt64 → List UInt8
  | [] => []
  | word :: rest => wordBytes word ++ wordsBytes rest
def serializerBytes (words : List UInt64) : List UInt8 := wordsBytes (sourceNormalize (nativeRounds 4 words))
def scalarKey (words : Vector UInt64 4) : Nat := decodeLE (serializerBytes words.toList)

theorem typed_little_endian_encoding_has_exact_width (width value : Nat) :
    (encodeLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    change (encodeLE width (value / 256)).length + 1 = width + 1
    rw [ih]

theorem little_endian_append_preserves_positional_value (left right : List UInt8) :
    decodeLE (left ++ right) = decodeLE left + 256 ^ left.length * decodeLE right := by
  induction left with
  | nil => simp only [List.nil_append, decodeLE, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons byte rest ih =>
    change byte.toNat + 256 * decodeLE (rest ++ right) =
      (byte.toNat + 256 * decodeLE rest) + 256 ^ (rest.length + 1) * decodeLE right
    rw [ih, Nat.pow_succ, Nat.mul_add]
    ac_rfl

theorem typed_little_endian_encoding_reconstructs_bounded_integer
    (width value : Nat) (bounded : value < 256 ^ width) : decodeLE (encodeLE width value) = value := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bounded)
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa only [Nat.pow_succ] using bounded)
    have remainder : value % 256 < 256 := Nat.mod_lt _ (by decide)
    change (value % 256) % 256 + 256 * decodeLE (encodeLE width (value / 256)) = value
    rw [Nat.mod_eq_of_lt remainder, ih _ quotient]
    exact Nat.mod_add_div value 256

theorem word_bytes_reconstruct_actual_finite_u64 (word : UInt64) : decodeLE (wordBytes word) = word.toNat := by
  exact typed_little_endian_encoding_reconstructs_bounded_integer 8 word.toNat word.toNat_lt

theorem serialized_word_vector_has_eight_bytes_per_word (words : List UInt64) :
    (wordsBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change (wordBytes word ++ wordsBytes rest).length = 8 * (rest.length + 1)
    rw [List.length_append, wordBytes, typed_little_endian_encoding_has_exact_width, ih, Nat.mul_add, Nat.mul_one]
    ac_rfl

theorem serialized_word_vector_reconstructs_actual_packed_words (words : List UInt64) :
    decodeLE (wordsBytes words) = packWords words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change decodeLE (wordBytes word ++ wordsBytes rest) = word.toNat + radix64 * packWords rest
    rw [little_endian_append_preserves_positional_value, word_bytes_reconstruct_actual_finite_u64,
      wordBytes, typed_little_endian_encoding_has_exact_width, ih]
    rfl

theorem source_scalar_serialization_has_exact_32_byte_width (words : List UInt64) (four : words.length = 4) :
    (serializerBytes words).length = 32 := by
  unfold serializerBytes
  rw [serialized_word_vector_has_eight_bytes_per_word,
    TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width _
      (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)]

theorem source_scalar_serialization_reconstructs_canonical_field_value (words : List UInt64) (four : words.length = 4) :
    decodeLE (serializerBytes words) < nullifierModulus := by
  unfold serializerBytes
  rw [serialized_word_vector_reconstructs_actual_packed_words]
  exact TransferScalarMaskedNormalization01.four_round_source_sub_and_addback_have_canonical_field_range words four

theorem fixed_four_word_source_scalar_projection_is_canonical (words : Vector UInt64 4) : scalarKey words < nullifierModulus := by
  exact source_scalar_serialization_reconstructs_canonical_field_value words.toList Vector.length_toList

set_option pp.all true in
#check @encodeLE
#print axioms encodeLE
set_option pp.all true in
#check @decodeLE
#print axioms decodeLE
set_option pp.all true in
#check @wordBytes
#print axioms wordBytes
set_option pp.all true in
#check @wordsBytes
#print axioms wordsBytes
set_option pp.all true in
#check @serializerBytes
#print axioms serializerBytes
set_option pp.all true in
#check @scalarKey
#print axioms scalarKey
set_option pp.all true in
#check @typed_little_endian_encoding_has_exact_width
#print axioms typed_little_endian_encoding_has_exact_width
set_option pp.all true in
#check @little_endian_append_preserves_positional_value
#print axioms little_endian_append_preserves_positional_value
set_option pp.all true in
#check @typed_little_endian_encoding_reconstructs_bounded_integer
#print axioms typed_little_endian_encoding_reconstructs_bounded_integer
set_option pp.all true in
#check @word_bytes_reconstruct_actual_finite_u64
#print axioms word_bytes_reconstruct_actual_finite_u64
set_option pp.all true in
#check @serialized_word_vector_has_eight_bytes_per_word
#print axioms serialized_word_vector_has_eight_bytes_per_word
set_option pp.all true in
#check @serialized_word_vector_reconstructs_actual_packed_words
#print axioms serialized_word_vector_reconstructs_actual_packed_words
set_option pp.all true in
#check @source_scalar_serialization_has_exact_32_byte_width
#print axioms source_scalar_serialization_has_exact_32_byte_width
set_option pp.all true in
#check @source_scalar_serialization_reconstructs_canonical_field_value
#print axioms source_scalar_serialization_reconstructs_canonical_field_value
set_option pp.all true in
#check @fixed_four_word_source_scalar_projection_is_canonical
#print axioms fixed_four_word_source_scalar_projection_is_canonical
end ShielddSecurity.TransferScalarLittleEndianBytes01
