import ShielddSecurity.TransferBlstArmInverseSignedWord01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignBit01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)

/-! Original factor word's bit63 extraction and sign predicate. Literal63
logical shift is interpreted by UInt64/BitVec arithmetic; signed factor code
decoding discharges integer sign correspondence. Actual arithmetic-shift mask,
factor XOR/subtract magnitude and compiled ISA remain separate obligations. -/

def sourceFactorTopBit (word : UInt64) : Nat := (word >>> 63).toNat

theorem original_factor_top_bit_is_the_exact_unsigned_half_radix_quotient (word : UInt64) :
    sourceFactorTopBit word=word.toNat/9223372036854775808 := by
  rw [sourceFactorTopBit,UInt64.toNat_shiftRight]
  have shift : (63:UInt64).toNat%64=63 := by decide
  rw [shift,Nat.shiftRight_eq_div_pow]

theorem original_factor_top_bit_is_binary_and_is_one_exactly_at_the_sign_threshold (word : UInt64) :
    sourceFactorTopBit word≤1 ∧ (sourceFactorTopBit word=1 ↔ 9223372036854775808≤word.toNat) := by
  rw [original_factor_top_bit_is_the_exact_unsigned_half_radix_quotient]
  have range := word.toNat_lt
  change word.toNat<18446744073709551616 at range
  constructor <;> omega

theorem original_coded_signed_factor_top_bit_is_one_exactly_when_the_factor_is_negative
    (value : Int) (lower : -9223372036854775808≤value) (upper : value<9223372036854775808) :
    sourceFactorTopBit (sourceSignedWordCode value)=1 ↔ value<0 := by
  exact (original_factor_top_bit_is_binary_and_is_one_exactly_at_the_sign_threshold (sourceSignedWordCode value)).2.trans
    (TransferBlstArmInverseSignedWord01.original_unsigned_factor_sign_threshold_is_exact_integer_negativity value lower upper)

set_option pp.all true in
#check @sourceFactorTopBit
#print axioms sourceFactorTopBit
set_option pp.all true in
#check @original_factor_top_bit_is_the_exact_unsigned_half_radix_quotient
#print axioms original_factor_top_bit_is_the_exact_unsigned_half_radix_quotient
set_option pp.all true in
#check @original_factor_top_bit_is_binary_and_is_one_exactly_at_the_sign_threshold
#print axioms original_factor_top_bit_is_binary_and_is_one_exactly_at_the_sign_threshold
set_option pp.all true in
#check @original_coded_signed_factor_top_bit_is_one_exactly_when_the_factor_is_negative
#print axioms original_coded_signed_factor_top_bit_is_one_exactly_when_the_factor_is_negative
end ShielddSecurity.TransferBlstArmInverseSignBit01
