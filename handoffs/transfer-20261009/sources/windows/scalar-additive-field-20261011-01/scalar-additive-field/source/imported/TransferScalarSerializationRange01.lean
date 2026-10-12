import ShielddSecurity.TransferNativeOnlyPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSerializationRange01
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic range bound for the four-round Montgomery reduction used by the
pinned BLS Scalar to_bytes implementation. The mathematical recurrence divides
the accumulated numerator by the word radix at each round, then conditionally
subtracts the modulus. No cancellation, primality or curve theorem is needed
for this range claim. Correspondence to Rust mac/adc/sbb, carry threading,
word packing and little-endian serialization is still an explicit interface.
This is a proof of the recurrence, not a native execution or certification. -/
def radix64 : Nat := 2 ^ 64

def reduceRounds (modulus radix : Nat) (accumulator : Nat) : List Nat → Nat
  | [] => accumulator
  | multiplier :: rest => reduceRounds modulus radix ((accumulator + multiplier * modulus) / radix) rest

def normalize (modulus accumulator : Nat) : Nat :=
  if modulus ≤ accumulator then accumulator - modulus else accumulator

theorem one_round_preserves_symbolic_range (modulus radix accumulator multiplier rounds : Nat)
    (positive : 0 < radix) (word : multiplier < radix)
    (initial : accumulator < modulus + radix ^ (rounds + 1)) :
    (accumulator + multiplier * modulus) / radix < modulus + radix ^ rounds := by
  apply (Nat.div_lt_iff_lt_mul positive).2
  calc
    accumulator + multiplier * modulus < (modulus + radix ^ (rounds + 1)) + multiplier * modulus := Nat.add_lt_add_right initial _
    _ = (multiplier + 1) * modulus + radix ^ rounds * radix := by
      simp only [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ radix * modulus + radix ^ rounds * radix := Nat.add_le_add_right (Nat.mul_le_mul_right modulus (Nat.succ_le_of_lt word)) _
    _ = (modulus + radix ^ rounds) * radix := by
      rw [Nat.add_mul, Nat.mul_comm radix modulus]

theorem all_rounds_finish_at_most_modulus (modulus radix : Nat) (digits : List Nat)
    (positive : 0 < radix) (words : ∀ digit ∈ digits, digit < radix)
    (accumulator : Nat) (initial : accumulator < modulus + radix ^ digits.length) :
    reduceRounds modulus radix accumulator digits < modulus + 1 := by
  induction digits generalizing accumulator with
  | nil => simpa only [reduceRounds, List.length_nil, Nat.pow_zero] using initial
  | cons digit rest ih =>
    apply ih
    · intro next inside
      exact words next (List.mem_cons_of_mem digit inside)
    · exact one_round_preserves_symbolic_range modulus radix accumulator digit rest.length
        positive (words digit List.mem_cons_self) initial

theorem final_subtraction_is_canonical (modulus accumulator : Nat)
    (positive : 0 < modulus) (bounded : accumulator < modulus + 1) :
    normalize modulus accumulator < modulus := by
  by_cases high : modulus ≤ accumulator
  · have exactModulus : accumulator = modulus := Nat.le_antisymm (Nat.le_of_lt_succ bounded) high
    subst accumulator
    simpa only [normalize, Nat.le_refl, if_true, Nat.sub_self] using positive
  · simpa only [normalize, high, if_false] using Nat.lt_of_not_ge high

theorem finite_word_vector_reduction_is_canonical (modulus radix : Nat)
    (positiveModulus : 0 < modulus) (positiveRadix : 0 < radix)
    (digits : List (Fin radix)) (accumulator : Nat)
    (rawBound : accumulator < radix ^ digits.length) :
    normalize modulus (reduceRounds modulus radix accumulator (digits.map Fin.val)) < modulus := by
  apply final_subtraction_is_canonical modulus _ positiveModulus
  apply all_rounds_finish_at_most_modulus modulus radix (digits.map Fin.val) positiveRadix
  · intro digit inside
    obtain ⟨word, _, value⟩ := List.mem_map.mp inside
    subst digit
    exact word.isLt
  · simpa only [List.length_map] using Nat.lt_of_lt_of_le rawBound (Nat.le_add_left _ _)

theorem four_u64_rounds_reduce_into_actual_nullifier_field
    (digits : List (Fin radix64)) (four : digits.length = 4)
    (raw : Nat) (fourWords : raw < radix64 ^ 4) :
    normalize nullifierModulus (reduceRounds nullifierModulus radix64 raw (digits.map Fin.val)) < nullifierModulus := by
  apply finite_word_vector_reduction_is_canonical nullifierModulus radix64 (by decide) (by decide) digits raw
  simpa only [four] using fourWords

set_option pp.all true in
#check @radix64
#print axioms radix64
set_option pp.all true in
#check @reduceRounds
#print axioms reduceRounds
set_option pp.all true in
#check @normalize
#print axioms normalize
set_option pp.all true in
#check @one_round_preserves_symbolic_range
#print axioms one_round_preserves_symbolic_range
set_option pp.all true in
#check @all_rounds_finish_at_most_modulus
#print axioms all_rounds_finish_at_most_modulus
set_option pp.all true in
#check @final_subtraction_is_canonical
#print axioms final_subtraction_is_canonical
set_option pp.all true in
#check @finite_word_vector_reduction_is_canonical
#print axioms finite_word_vector_reduction_is_canonical
set_option pp.all true in
#check @four_u64_rounds_reduce_into_actual_nullifier_field
#print axioms four_u64_rounds_reduce_into_actual_nullifier_field
end ShielddSecurity.TransferScalarSerializationRange01
