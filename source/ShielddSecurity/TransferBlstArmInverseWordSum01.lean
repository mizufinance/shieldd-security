import ShielddSecurity.TransferBlstArmInverseSignedWordMultiply01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordSum01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
attribute [local irreducible] sourceAddCarryChain

/-! Equal-width source word addition, with its final arithmetic carry retained.
This is an arithmetic source model; instruction execution remains separate. -/

def sourceWordSum (left right : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false (left.zip right)

theorem equal_width_source_word_addition_retains_the_entire_output_width
    (left right : List UInt64) (same : left.length = right.length) :
    (sourceWordSum left right).1.length = left.length := by
  simp only [sourceWordSum, TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip, ←same, Nat.min_self]

theorem equal_width_source_word_addition_conserves_the_full_sum_and_final_carry
    (left right : List UInt64) (same : left.length = right.length) :
    packWords (sourceWordSum left right).1 +
      radix64 ^ left.length * (sourceWordSum left right).2.toNat =
        packWords left + packWords right := by
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (left.zip right)
  rw [List.map_fst_zip (Nat.le_of_eq same), List.map_snd_zip (Nat.le_of_eq same.symm),
    List.length_zip, ←same, Nat.min_self] at conserved
  change packWords (sourceWordSum left right).1 +
    radix64 ^ left.length * (sourceWordSum left right).2.toNat =
      packWords left + packWords right + 0 at conserved
  exact conserved.trans (Nat.add_zero _)

attribute [local irreducible] sourceWordSum

theorem equal_width_source_word_addition_retains_the_full_integer_sum_residue
    (left right : List UInt64) (same : left.length = right.length) :
    (packWords (sourceWordSum left right).1 : Int) % ((radix64 ^ left.length : Nat) : Int) =
      ((packWords left : Int) + (packWords right : Int)) % ((radix64 ^ left.length : Nat) : Int) := by
  have conserved := equal_width_source_word_addition_conserves_the_full_sum_and_final_carry left right same
  have cast := congrArg (fun value : Nat => (value : Int)) conserved
  simp only [Nat.cast_add, Nat.cast_mul] at cast
  have reduced := congrArg (fun value : Int => value % ((radix64 ^ left.length : Nat) : Int)) cast
  dsimp only at reduced
  rw [Int.add_mul_emod_self_left] at reduced
  exact reduced

set_option pp.all true in
#check @sourceWordSum
#print axioms sourceWordSum
set_option pp.all true in
#check @equal_width_source_word_addition_retains_the_entire_output_width
#print axioms equal_width_source_word_addition_retains_the_entire_output_width
set_option pp.all true in
#check @equal_width_source_word_addition_conserves_the_full_sum_and_final_carry
#print axioms equal_width_source_word_addition_conserves_the_full_sum_and_final_carry
set_option pp.all true in
#check @equal_width_source_word_addition_retains_the_full_integer_sum_residue
#print axioms equal_width_source_word_addition_retains_the_full_integer_sum_residue
end ShielddSecurity.TransferBlstArmInverseWordSum01
