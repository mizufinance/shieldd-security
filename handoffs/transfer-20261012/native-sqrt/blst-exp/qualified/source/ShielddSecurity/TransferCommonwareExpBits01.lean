import ShielddSecurity.TransferCommonwareSqrtComplete01
import ShielddSecurity.TransferScalarPowBitInteger01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareExpBits01
open TransferScalarPowInvariant01 (sourcePowBit)
open TransferScalarPowBitInteger01
open TransferScalarWordPrimitives01 (packWords)
open TransferCommonwareSqrtComplete01 (sourceCommonwareExponent)

def bitNumber : List Bool → Nat
  | [] => 0
  | b::rest => (if b then 1 else 0)+2*bitNumber rest

theorem reverse_binary_fold_reconstructs_the_little_endian_bit_number (bits : List Bool) (seed : Nat) :
    bits.reverse.foldl (fun value b => value*2+(if b then 1 else 0)) seed =
      seed*2^bits.length+bitNumber bits := by
  induction bits generalizing seed with
  | nil => simp [bitNumber]
  | cons b rest ih =>
    rw [List.reverse_cons,List.foldl_append,ih]
    simp only [List.foldl_cons,List.foldl_nil,List.length_cons,bitNumber,Nat.pow_succ]
    ring

theorem little_endian_bit_numbers_compose_at_the_exact_prefix_width (left right : List Bool) :
    bitNumber (left++right) = bitNumber left + 2^left.length*bitNumber right := by
  induction left with
  | nil => simp [bitNumber]
  | cons b rest ih =>
    simp only [List.cons_append,bitNumber,List.length_cons,ih,Nat.pow_succ]
    ring

def sourceWordBits (word : UInt64) (count : Nat) : List Bool := (List.range count).map (sourcePowBit word)

theorem exact_source_little_endian_word_bits_reconstruct_the_low_integer
    (word : UInt64) (count : Nat) (bounded : count ≤ 64) :
    bitNumber (sourceWordBits word count) = word.toNat % 2^count := by
  have value := reverse_binary_fold_reconstructs_the_little_endian_bit_number (sourceWordBits word count) 0
  simp only [Nat.zero_mul,Nat.zero_add] at value
  rw [sourceWordBits,← List.map_reverse,List.foldl_map] at value
  have agree := symbolic_natural_folds_agree_from_actual_member_steps (List.range count).reverse 0
    (fun current index => current*2+(if sourcePowBit word index then 1 else 0))
    (fun current index => current*2+(word.toNat/2^index)%2)
    (by
      intro current index member
      have lower := List.mem_range.mp (List.mem_reverse.mp member)
      simp only [bounded_source_word_boolean_bit_has_exact_binary_digit word index (by omega)])
  rw [agree,symbolic_high_to_low_binary_digit_walk_reconstructs_exact_low_bits] at value
  simpa only [Nat.zero_mul,Nat.zero_add] using value.symm

def sourceSqrtExponentBits : List Bool :=
  sourceWordBits sourceCommonwareExponent[0] 64 ++
    sourceWordBits sourceCommonwareExponent[1] 64 ++
    sourceWordBits sourceCommonwareExponent[2] 64 ++
    sourceWordBits sourceCommonwareExponent[3] 30

theorem exact_commonware_last_sqrt_word_has_thirty_significant_bits :
    2^29 ≤ sourceCommonwareExponent[3].toNat ∧ sourceCommonwareExponent[3].toNat < 2^30 := by decide

theorem exact_commonware_sqrt_bit_iterator_has_222_steps : sourceSqrtExponentBits.length = 222 := by
  simp [sourceSqrtExponentBits,sourceWordBits]

theorem exact_commonware_sqrt_bit_iterator_reconstructs_the_locked_exponent :
    bitNumber sourceSqrtExponentBits = packWords sourceCommonwareExponent.toList := by
  have width : ∀ word : UInt64, ∀ count : Nat, (sourceWordBits word count).length = count := by
    intro word count
    simp only [sourceWordBits,List.length_map,List.length_range]
  rw [sourceSqrtExponentBits]
  simp only [little_endian_bit_numbers_compose_at_the_exact_prefix_width,
    width]
  rw [exact_source_little_endian_word_bits_reconstruct_the_low_integer _ 64 (by decide),
    exact_source_little_endian_word_bits_reconstruct_the_low_integer _ 64 (by decide),
    exact_source_little_endian_word_bits_reconstruct_the_low_integer _ 64 (by decide),
    exact_source_little_endian_word_bits_reconstruct_the_low_integer _ 30 (by decide)]
  decide +kernel

set_option pp.all true in
#check @bitNumber
#print axioms bitNumber
set_option pp.all true in
#check @reverse_binary_fold_reconstructs_the_little_endian_bit_number
#print axioms reverse_binary_fold_reconstructs_the_little_endian_bit_number
set_option pp.all true in
#check @little_endian_bit_numbers_compose_at_the_exact_prefix_width
#print axioms little_endian_bit_numbers_compose_at_the_exact_prefix_width
set_option pp.all true in
#check @sourceWordBits
#print axioms sourceWordBits
set_option pp.all true in
#check @exact_source_little_endian_word_bits_reconstruct_the_low_integer
#print axioms exact_source_little_endian_word_bits_reconstruct_the_low_integer
set_option pp.all true in
#check @sourceSqrtExponentBits
#print axioms sourceSqrtExponentBits
set_option pp.all true in
#check @exact_commonware_last_sqrt_word_has_thirty_significant_bits
#print axioms exact_commonware_last_sqrt_word_has_thirty_significant_bits
set_option pp.all true in
#check @exact_commonware_sqrt_bit_iterator_has_222_steps
#print axioms exact_commonware_sqrt_bit_iterator_has_222_steps
set_option pp.all true in
#check @exact_commonware_sqrt_bit_iterator_reconstructs_the_locked_exponent
#print axioms exact_commonware_sqrt_bit_iterator_reconstructs_the_locked_exponent
end ShielddSecurity.TransferCommonwareExpBits01
