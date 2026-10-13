import ShielddSecurity.TransferBlstByteRoundtrip01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmProducts01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords mac128 split128)

/-- Arithmetic low/high products of the locked ARM64 MUL/UMULH pairs.
Native instruction execution, register allocation and ABI are separate. -/
def sourceProductSplit (multiplier operand : UInt64) : UInt64 × UInt64 :=
  split128 (mac128 0 multiplier operand 0)

theorem actual_product_low_and_high_words_conserve_the_full_integer
    (multiplier operand : UInt64) :
    (sourceProductSplit multiplier operand).1.toNat+
      radix64*(sourceProductSplit multiplier operand).2.toNat = multiplier.toNat*operand.toNat := by
  simpa only [sourceProductSplit,UInt64.toNat_zero,Nat.zero_add,Nat.add_zero] using
    TransferScalarWordPrimitives01.widened_u64_mac_low_word_and_carry_conserve_value 0 multiplier operand 0

theorem actual_product_low_word_is_the_source_wrapped_mul
    (multiplier operand : UInt64) : (sourceProductSplit multiplier operand).1 = multiplier*operand := by
  apply UInt64.toNat_inj.mp
  simp only [sourceProductSplit,split128,UInt64.toNat_ofNat',
    TransferScalarWordPrimitives01.widened_u64_mac_preserves_full_integer,
    UInt64.toNat_zero,Nat.zero_add,Nat.add_zero,UInt64.toNat_mul]

def sourceProductLowWords (multiplier : UInt64) (words : List UInt64) : List UInt64 :=
  words.map (fun operand => (sourceProductSplit multiplier operand).1)
def sourceProductHighWords (multiplier : UInt64) (words : List UInt64) : List UInt64 :=
  words.map (fun operand => (sourceProductSplit multiplier operand).2)

theorem source_product_vectors_retain_the_source_modulus_limb_count
    (multiplier : UInt64) (words : List UInt64) :
    (sourceProductLowWords multiplier words).length = words.length ∧
      (sourceProductHighWords multiplier words).length = words.length := by
  exact ⟨List.length_map _,List.length_map _⟩

theorem symbolic_packed_low_and_high_product_vectors_conserve_the_full_product
    (multiplier : UInt64) (words : List UInt64) :
    packWords (sourceProductLowWords multiplier words)+
      radix64*packWords (sourceProductHighWords multiplier words) = multiplier.toNat*packWords words := by
  induction words with
  | nil => simp only [sourceProductLowWords,sourceProductHighWords,List.map_nil,packWords,Nat.mul_zero,Nat.zero_add]
  | cons word rest ih =>
    have first := actual_product_low_and_high_words_conserve_the_full_integer multiplier word
    change (sourceProductSplit multiplier word).1.toNat+
        radix64*packWords (sourceProductLowWords multiplier rest)+
        radix64*((sourceProductSplit multiplier word).2.toNat+
          radix64*packWords (sourceProductHighWords multiplier rest)) =
      multiplier.toNat*(word.toNat+radix64*packWords rest)
    calc
      _ = ((sourceProductSplit multiplier word).1.toNat+
          radix64*(sourceProductSplit multiplier word).2.toNat)+
          radix64*(packWords (sourceProductLowWords multiplier rest)+
            radix64*packWords (sourceProductHighWords multiplier rest)) := by ring
      _ = multiplier.toNat*word.toNat+radix64*(multiplier.toNat*packWords rest) := by rw [first,ih]
      _ = _ := by ring
set_option pp.all true in
#check @sourceProductSplit
#print axioms sourceProductSplit
set_option pp.all true in
#check @actual_product_low_and_high_words_conserve_the_full_integer
#print axioms actual_product_low_and_high_words_conserve_the_full_integer
set_option pp.all true in
#check @actual_product_low_word_is_the_source_wrapped_mul
#print axioms actual_product_low_word_is_the_source_wrapped_mul
set_option pp.all true in
#check @sourceProductLowWords
#print axioms sourceProductLowWords
set_option pp.all true in
#check @sourceProductHighWords
#print axioms sourceProductHighWords
set_option pp.all true in
#check @source_product_vectors_retain_the_source_modulus_limb_count
#print axioms source_product_vectors_retain_the_source_modulus_limb_count
set_option pp.all true in
#check @symbolic_packed_low_and_high_product_vectors_conserve_the_full_product
#print axioms symbolic_packed_low_and_high_product_vectors_conserve_the_full_product
end ShielddSecurity.TransferBlstArmProducts01
