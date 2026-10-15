import ShielddSecurity.TransferBlstArmInverseFactors01
import Mathlib.Tactic.SplitIfs
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedWord01

/-! Integer interpretation of signed64 factor register codes. The unsigned
code is the original two's-complement residue, and threshold decoding derives
the entire signed value and sign guard within the explicit signed64 domain.
Packed slot subtraction, actual ASR/word multiply and ISA execution remain
separate obligations. No native execution/certification credit is inferred. -/

def sourceSignedWordCode (value : Int) : UInt64 :=
  UInt64.ofNat ((value%18446744073709551616).toNat)

def sourceSignedWordMeaning (word : UInt64) : Int :=
  if 9223372036854775808≤word.toNat then (word.toNat:Int)-18446744073709551616
  else (word.toNat:Int)

theorem original_signed64_word_code_has_the_entire_integer_modulo_residue (value : Int) :
    ((sourceSignedWordCode value).toNat:Int)=value%18446744073709551616 := by
  have nonnegative := Int.emod_nonneg value (by decide : (18446744073709551616:Int)≠0)
  have bounded := Int.emod_lt_of_pos value (by decide : (0:Int)<18446744073709551616)
  have natBound : (value%18446744073709551616).toNat<UInt64.size := by
    change (value%18446744073709551616).toNat<18446744073709551616
    omega
  rw [sourceSignedWordCode,UInt64.toNat_ofNat_of_lt' natBound]
  exact Int.toNat_of_nonneg nonnegative

theorem original_signed64_code_and_threshold_decode_recover_the_entire_factor_value
    (value : Int) (lower : -9223372036854775808≤value) (upper : value<9223372036854775808) :
    sourceSignedWordMeaning (sourceSignedWordCode value)=value := by
  have code := original_signed64_word_code_has_the_entire_integer_modulo_residue value
  by_cases nonnegative : 0≤value
  · have within : value<18446744073709551616 := by omega
    rw [Int.emod_eq_of_lt nonnegative within] at code
    have guard : ¬9223372036854775808≤(sourceSignedWordCode value).toNat := by omega
    rw [sourceSignedWordMeaning,if_neg guard]
    exact code
  · have shiftedNonnegative : 0≤value+18446744073709551616 := by omega
    have shiftedBounded : value+18446744073709551616<18446744073709551616 := by omega
    have period := Int.add_emod_right value 18446744073709551616
    rw [Int.emod_eq_of_lt shiftedNonnegative shiftedBounded] at period
    rw [← period] at code
    have guard : 9223372036854775808≤(sourceSignedWordCode value).toNat := by omega
    rw [sourceSignedWordMeaning,if_pos guard,code]
    omega

theorem original_unsigned_factor_sign_threshold_is_exact_integer_negativity
    (value : Int) (lower : -9223372036854775808≤value) (upper : value<9223372036854775808) :
    9223372036854775808≤(sourceSignedWordCode value).toNat ↔ value<0 := by
  have full := original_signed64_code_and_threshold_decode_recover_the_entire_factor_value value lower upper
  have rawBound := (sourceSignedWordCode value).toNat_lt
  change (sourceSignedWordCode value).toNat<18446744073709551616 at rawBound
  rw [sourceSignedWordMeaning] at full
  split_ifs at full <;> omega

set_option pp.all true in
#check @sourceSignedWordCode
#print axioms sourceSignedWordCode
set_option pp.all true in
#check @sourceSignedWordMeaning
#print axioms sourceSignedWordMeaning
set_option pp.all true in
#check @original_signed64_word_code_has_the_entire_integer_modulo_residue
#print axioms original_signed64_word_code_has_the_entire_integer_modulo_residue
set_option pp.all true in
#check @original_signed64_code_and_threshold_decode_recover_the_entire_factor_value
#print axioms original_signed64_code_and_threshold_decode_recover_the_entire_factor_value
set_option pp.all true in
#check @original_unsigned_factor_sign_threshold_is_exact_integer_negativity
#print axioms original_unsigned_factor_sign_threshold_is_exact_integer_negativity
end ShielddSecurity.TransferBlstArmInverseSignedWord01
