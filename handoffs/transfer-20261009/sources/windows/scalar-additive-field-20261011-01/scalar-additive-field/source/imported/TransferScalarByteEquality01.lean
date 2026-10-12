import ShielddSecurity.TransferScalarPaddedCarry01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarByteEquality01
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Equality of exact finite source serializer byte keys and mathematical
Montgomery values. Typed UInt8 bounds derive exact head/remainder and
tail/quotient observations. A symbolic equal-width induction proves decoder
injectivity without a caller-provided byte-validity premise. The source
32-byte width and exact canonical projection then give equality equivalence.
Rust primitive/to_le_bytes/trace/type/library and native key correspondence
remain separate; no hash collision freedom or native control is claimed. -/

theorem typed_little_endian_head_is_exact_numeric_remainder (byte : UInt8) (rest : List UInt8) :
    decodeLE (byte :: rest) % 256 = byte.toNat := by
  change (byte.toNat + 256 * decodeLE rest) % 256 = byte.toNat
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt byte.toNat_lt

theorem typed_little_endian_tail_is_exact_numeric_quotient (byte : UInt8) (rest : List UInt8) :
    decodeLE (byte :: rest) / 256 = decodeLE rest := by
  have bounded : byte.toNat < 256 := byte.toNat_lt
  change (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt bounded, Nat.zero_add]

theorem typed_little_endian_decoder_is_injective_at_equal_width
    (left right : List UInt8) (width : left.length = right.length)
    (value : decodeLE left = decodeLE right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons byte rest => simp only [List.length_nil, List.length_cons] at width; omega
  | cons byte rest ih =>
    cases right with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons other tail =>
      have first := congrArg (fun n => n % 256) value
      change decodeLE (byte :: rest) % 256 = decodeLE (other :: tail) % 256 at first
      rw [typed_little_endian_head_is_exact_numeric_remainder,
        typed_little_endian_head_is_exact_numeric_remainder] at first
      have equalByte : byte = other := UInt8.toNat_inj.mp first
      have remaining := congrArg (fun n => n / 256) value
      change decodeLE (byte :: rest) / 256 = decodeLE (other :: tail) / 256 at remaining
      rw [typed_little_endian_tail_is_exact_numeric_quotient,
        typed_little_endian_tail_is_exact_numeric_quotient] at remaining
      have tailWidth : rest.length = tail.length := by
        simp only [List.length_cons] at width
        omega
      rw [equalByte, ih tail tailWidth remaining]

theorem source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal
    (left right : Vector UInt64 4) :
    serializerBytes left.toList = serializerBytes right.toList ↔
      montgomeryValue left = montgomeryValue right := by
  constructor
  · intro equalBytes
    have equalValue := congrArg decodeLE equalBytes
    change scalarKey left = scalarKey right at equalValue
    rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
      TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value] at equalValue
    exact equalValue
  · intro equalValue
    apply typed_little_endian_decoder_is_injective_at_equal_width
    · rw [TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList,
        TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList]
    · change scalarKey left = scalarKey right
      rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
        TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
      exact equalValue

set_option pp.all true in
#check @typed_little_endian_head_is_exact_numeric_remainder
#print axioms typed_little_endian_head_is_exact_numeric_remainder
set_option pp.all true in
#check @typed_little_endian_tail_is_exact_numeric_quotient
#print axioms typed_little_endian_tail_is_exact_numeric_quotient
set_option pp.all true in
#check @typed_little_endian_decoder_is_injective_at_equal_width
#print axioms typed_little_endian_decoder_is_injective_at_equal_width
set_option pp.all true in
#check @source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal
#print axioms source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal
end ShielddSecurity.TransferScalarByteEquality01
