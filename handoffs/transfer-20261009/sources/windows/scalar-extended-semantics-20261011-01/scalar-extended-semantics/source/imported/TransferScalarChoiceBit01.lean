import ShielddSecurity.TransferScalarByteDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarChoiceBit01
open TransferScalarSbbPrimitive01 (borrowMask)
open TransferScalarByteDecode01 (sourceCanonicalBorrowAccepts)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped low choice bit `(borrow as u8) & 1` follows the exact
zero/all-ones finite u64 mask. Derive both canonical success bit and refusal
bit from the parsed byte value, without supplying either flag. The model
does not claim actual CtOption/Choice construction or R2 payload conversion,
Scalar invariant/native primitive/compiler/full trace binding. -/

def borrowChoiceByte (borrow : Bool) : UInt8 :=
  UInt8.ofNat (borrowMask borrow).toNat &&& 1

theorem source_borrow_choice_byte_is_exact_zero_or_one (borrow : Bool) :
    borrowChoiceByte borrow = (if borrow then 1 else 0) := by
  cases borrow <;> decide

theorem source_borrow_choice_byte_is_one_exactly_on_underflow (borrow : Bool) :
    borrowChoiceByte borrow = 1 ↔ borrow = true := by
  cases borrow <;> decide

theorem source_borrow_choice_byte_is_zero_exactly_without_underflow (borrow : Bool) :
    borrowChoiceByte borrow = 0 ↔ borrow = false := by
  cases borrow <;> decide

def sourceCanonicalChoiceByte (bytes : Vector UInt8 32) : UInt8 :=
  borrowChoiceByte (sourceCanonicalBorrowAccepts bytes)

theorem source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus (bytes : Vector UInt8 32) :
    sourceCanonicalChoiceByte bytes = 1 ↔ decodeLE bytes.toList < nullifierModulus := by
  rw [sourceCanonicalChoiceByte, source_borrow_choice_byte_is_one_exactly_on_underflow,
    TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer]

theorem source_canonical_choice_byte_is_zero_iff_parsed_integer_is_noncanonical (bytes : Vector UInt8 32) :
    sourceCanonicalChoiceByte bytes = 0 ↔ ¬ decodeLE bytes.toList < nullifierModulus := by
  rw [sourceCanonicalChoiceByte, source_borrow_choice_byte_is_zero_exactly_without_underflow]
  have accepted := TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer bytes
  constructor
  · intro no less
    have yes := accepted.mpr less
    rw [no] at yes
    cases yes
  · intro noncanonical
    cases observed : sourceCanonicalBorrowAccepts bytes with
    | false => rfl
    | true => exact False.elim (noncanonical (accepted.mp observed))

theorem exact_source_serializer_bytes_derive_one_choice_byte
    (words : Vector UInt64 4) (bytes : Vector UInt8 32) (encoded : bytes.toList = serializerBytes words.toList) :
    sourceCanonicalChoiceByte bytes = 1 := by
  apply (source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes).mpr
  exact (TransferScalarByteDecode01.source_four_word_byte_decode_accepts_exact_canonical_integer bytes).mp
    (TransferScalarByteDecode01.exact_source_serializer_bytes_pass_the_source_canonical_borrow_predicate words bytes encoded)

set_option pp.all true in
#check @borrowChoiceByte
#print axioms borrowChoiceByte
set_option pp.all true in
#check @source_borrow_choice_byte_is_exact_zero_or_one
#print axioms source_borrow_choice_byte_is_exact_zero_or_one
set_option pp.all true in
#check @source_borrow_choice_byte_is_one_exactly_on_underflow
#print axioms source_borrow_choice_byte_is_one_exactly_on_underflow
set_option pp.all true in
#check @source_borrow_choice_byte_is_zero_exactly_without_underflow
#print axioms source_borrow_choice_byte_is_zero_exactly_without_underflow
set_option pp.all true in
#check @sourceCanonicalChoiceByte
#print axioms sourceCanonicalChoiceByte
set_option pp.all true in
#check @source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus
#print axioms source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus
set_option pp.all true in
#check @source_canonical_choice_byte_is_zero_iff_parsed_integer_is_noncanonical
#print axioms source_canonical_choice_byte_is_zero_iff_parsed_integer_is_noncanonical
set_option pp.all true in
#check @exact_source_serializer_bytes_derive_one_choice_byte
#print axioms exact_source_serializer_bytes_derive_one_choice_byte
end ShielddSecurity.TransferScalarChoiceBit01
