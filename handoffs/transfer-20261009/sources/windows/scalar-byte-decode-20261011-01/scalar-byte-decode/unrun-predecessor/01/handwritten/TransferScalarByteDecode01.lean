import ShielddSecurity.TransferPartitionLocalRollback01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarByteDecode01
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic typed-byte decoder reads consecutive eight-byte LE words.
Full reconstruction and exact canonical borrow acceptance are derived,
including rejection of values at/above p; no byte-range or desired flag is
supplied. Native from_le_bytes/SBB/mask/Choice/CtOption/field representation,
R2 Montgomery conversion/compiler/full trace bindings remain explicit. -/

def decodeLEWords : Nat → List UInt8 → List UInt64
  | 0, _ => []
  | count + 1, bytes => UInt64.ofNat (decodeLE (bytes.take 8)) :: decodeLEWords count (bytes.drop 8)

theorem typed_byte_decode_is_below_positional_width (bytes : List UInt8) :
    decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons head rest ih =>
    have bounded : head.toNat < 256 := head.toNat_lt
    change head.toNat + 256 * decodeLE rest < 256 ^ (rest.length + 1)
    rw [Nat.pow_succ]
    omega

theorem decoded_word_list_has_exact_requested_width (count : Nat) (bytes : List UInt8) :
    (decodeLEWords count bytes).length = count := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    change (decodeLEWords count (bytes.drop 8)).length + 1 = count + 1
    rw [ih]

theorem full_width_word_decoder_reconstructs_exact_little_endian_value
    (count : Nat) (bytes : List UInt8) (width : bytes.length = 8 * count) :
    packWords (decodeLEWords count bytes) = decodeLE bytes := by
  induction count generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.eq_nil_of_length_eq_zero width
    subst bytes
    rfl
  | succ count ih =>
    have enough : 8 ≤ bytes.length := by omega
    have taken : (bytes.take 8).length = 8 := by rw [List.length_take, Nat.min_eq_left enough]
    have dropped : (bytes.drop 8).length = 8 * count := by rw [List.length_drop]; omega
    have bounded := typed_byte_decode_is_below_positional_width (bytes.take 8)
    rw [taken] at bounded
    have wordBound : decodeLE (bytes.take 8) < radix64 := bounded
    have joined := TransferScalarLittleEndianBytes01.little_endian_append_preserves_positional_value (bytes.take 8) (bytes.drop 8)
    rw [List.take_append_drop, taken] at joined
    change decodeLE (bytes.take 8) % radix64 + radix64 * packWords (decodeLEWords count (bytes.drop 8)) = decodeLE bytes
    rw [Nat.mod_eq_of_lt wordBound, ih _ dropped]
    exact joined.symm

def sourceCanonicalBorrowAccepts (bytes : Vector UInt8 32) : Bool :=
  (borrowWalk false ((decodeLEWords 4 bytes.toList).zip modulusWords)).2

theorem source_four_word_byte_decode_accepts_exact_canonical_integer (bytes : Vector UInt8 32) :
    sourceCanonicalBorrowAccepts bytes = true ↔ decodeLE bytes.toList < nullifierModulus := by
  have decodedWidth : (decodeLEWords 4 bytes.toList).length = 4 := decoded_word_list_has_exact_requested_width 4 bytes.toList
  have equalWidths : (decodeLEWords 4 bytes.toList).length = modulusWords.length :=
    decodedWidth.trans TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs.symm
  change (borrowWalk false ((decodeLEWords 4 bytes.toList).zip modulusWords)).2 = true ↔ _
  rw [TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow,
    List.map_fst_zip (Nat.le_of_eq equalWidths), List.map_snd_zip (Nat.le_of_eq equalWidths.symm),
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus,
    full_width_word_decoder_reconstructs_exact_little_endian_value 4 bytes.toList Vector.length_toList]

theorem exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate
    (words : Vector UInt64 4) (bytes : Vector UInt8 32) (encoded : bytes.toList = serializerBytes words.toList) :
    sourceCanonicalBorrowAccepts bytes = true := by
  apply (source_four_word_byte_decode_accepts_exact_canonical_integer bytes).mpr
  rw [encoded]
  change scalarKey words < nullifierModulus
  exact TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_is_canonical words

set_option pp.all true in
#check @decodeLEWords
#print axioms decodeLEWords
set_option pp.all true in
#check @typed_byte_decode_is_below_positional_width
#print axioms typed_byte_decode_is_below_positional_width
set_option pp.all true in
#check @decoded_word_list_has_exact_requested_width
#print axioms decoded_word_list_has_exact_requested_width
set_option pp.all true in
#check @full_width_word_decoder_reconstructs_exact_little_endian_value
#print axioms full_width_word_decoder_reconstructs_exact_little_endian_value
set_option pp.all true in
#check @sourceCanonicalBorrowAccepts
#print axioms sourceCanonicalBorrowAccepts
set_option pp.all true in
#check @source_four_word_byte_decode_accepts_exact_canonical_integer
#print axioms source_four_word_byte_decode_accepts_exact_canonical_integer
set_option pp.all true in
#check @exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate
#print axioms exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate
end ShielddSecurity.TransferScalarByteDecode01
