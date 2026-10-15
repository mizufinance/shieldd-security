import ShielddSecurity.TransferBlstArmInverseNaturalTermination01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordRepack01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! Exact UInt64 repacking for repeated source batches. A symbolic radix
recurrence reconstructs every value below its capacity. Four-word repacking
and low-word oddness follow without selected word observations. Native
stores, aliasing and loads remain separate obligations. -/

def sourceWordsOfNat : Nat → Nat → List UInt64
  | 0, _ => []
  | count + 1, input => UInt64.ofNat input :: sourceWordsOfNat count (input / radix64)

def sourceFourWordsOfNat (input : Nat) : SourceFourWords :=
  ⟨UInt64.ofNat input, UInt64.ofNat (input / radix64),
   UInt64.ofNat (input / radix64 / radix64), UInt64.ofNat (input / radix64 / radix64 / radix64)⟩

theorem symbolic_natural_word_repacking_and_the_final_quotient_conserve_the_entire_input
    (count input : Nat) :
    packWords (sourceWordsOfNat count input) + radix64 ^ count * (input / radix64 ^ count) = input := by
  induction count generalizing input with
  | zero => simp only [sourceWordsOfNat, packWords, Nat.pow_zero, Nat.div_one, Nat.one_mul, Nat.zero_add]
  | succ count ih =>
    have previous := ih (input / radix64)
    have quotient : input / radix64 / radix64 ^ count = input / radix64 ^ (count + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (radix64 ^ count) radix64]
    have lifted := congrArg (fun value : Nat => radix64 * value) previous
    dsimp only at lifted
    rw [Nat.mul_add, ←Nat.mul_assoc, quotient] at lifted
    have power : radix64 ^ (count + 1) = radix64 * radix64 ^ count := by rw [Nat.pow_succ, Nat.mul_comm]
    have head : (UInt64.ofNat input).toNat = input % radix64 := UInt64.toNat_ofNat'
    change (UInt64.ofNat input).toNat + radix64 * packWords (sourceWordsOfNat count (input / radix64)) +
      radix64 ^ (count + 1) * (input / radix64 ^ (count + 1)) = input
    rw [head, power]
    rw [power] at lifted
    rw [Nat.add_assoc, lifted]
    exact Nat.mod_add_div input radix64

theorem natural_word_repacking_below_capacity_reconstructs_the_exact_input
    (count input : Nat) (bounded : input < radix64 ^ count) :
    packWords (sourceWordsOfNat count input) = input := by
  have entire := symbolic_natural_word_repacking_and_the_final_quotient_conserve_the_entire_input count input
  rw [Nat.div_eq_of_lt bounded, Nat.mul_zero, Nat.add_zero] at entire
  exact entire

theorem original_four_word_repacking_reconstructs_every_input_below_two256
    (input : Nat) (bounded : input < 2 ^ 256) :
    sourcePackedFourWords (sourceFourWordsOfNat input) = input := by
  have power : radix64 ^ 4 = (2 : Nat) ^ 256 := by simp only [radix64, ←Nat.pow_mul]
  change packWords (sourceWordsOfNat 4 input) = input
  exact natural_word_repacking_below_capacity_reconstructs_the_exact_input 4 input (by rw [power]; exact bounded)

theorem an_odd_natural_input_has_an_odd_original_repacked_low_word
    (input : Nat) (odd : input % 2 = 1) : (sourceFourWordsOfNat input).w0.toNat % 2 = 1 := by
  change (UInt64.ofNat input).toNat % 2 = 1
  have head : (UInt64.ofNat input).toNat = input % radix64 := UInt64.toNat_ofNat'
  have divisor : (2 : Nat) ∣ radix64 := by decide +kernel
  rw [head, Nat.mod_mod_of_dvd _ divisor, odd]

set_option pp.all true in
#check @sourceWordsOfNat
#print axioms sourceWordsOfNat
set_option pp.all true in
#check @sourceFourWordsOfNat
#print axioms sourceFourWordsOfNat
set_option pp.all true in
#check @symbolic_natural_word_repacking_and_the_final_quotient_conserve_the_entire_input
#print axioms symbolic_natural_word_repacking_and_the_final_quotient_conserve_the_entire_input
set_option pp.all true in
#check @natural_word_repacking_below_capacity_reconstructs_the_exact_input
#print axioms natural_word_repacking_below_capacity_reconstructs_the_exact_input
set_option pp.all true in
#check @original_four_word_repacking_reconstructs_every_input_below_two256
#print axioms original_four_word_repacking_reconstructs_every_input_below_two256
set_option pp.all true in
#check @an_odd_natural_input_has_an_odd_original_repacked_low_word
#print axioms an_odd_natural_input_has_an_odd_original_repacked_low_word
end ShielddSecurity.TransferBlstArmInverseWordRepack01
