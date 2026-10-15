import ShielddSecurity.TransferBlstArmInverseExtrChain01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedExtrQuotient01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
attribute [local irreducible] sourceExtractChain

/-! Dropping the extra high word after a sub-word shift preserves the signed
integer quotient modulo the retained word width. This uses an exact input
residue, without assuming the unsigned representation is nonnegative as a
signed integer. Native execution and the row/input origins remain separate. -/

theorem equal_entire_residues_derive_an_exact_integer_period_difference
    (unsigned value capacity : Int) (residue : unsigned % capacity = value % capacity) :
    ∃ multiple : Int, unsigned = value + capacity * multiple := by
  refine ⟨unsigned / capacity - value / capacity, ?_⟩
  calc
    unsigned = unsigned % capacity + capacity * (unsigned / capacity) := (Int.emod_add_mul_ediv _ _).symm
    _ = (value % capacity + capacity * (value / capacity)) +
        capacity * (unsigned / capacity - value / capacity) := by rw [residue]; ring1
    _ = _ := by rw [Int.emod_add_mul_ediv]

theorem a_factored_entire_capacity_derives_the_exact_signed_quotient_residue
    (unsigned value divisor outputCapacity extra : Int) (nonzero : divisor ≠ 0)
    (residue : unsigned % (divisor * (outputCapacity * extra)) =
      value % (divisor * (outputCapacity * extra))) :
    (unsigned / divisor) % outputCapacity = (value / divisor) % outputCapacity := by
  obtain ⟨multiple, whole⟩ := equal_entire_residues_derive_an_exact_integer_period_difference
    unsigned value (divisor * (outputCapacity * extra)) residue
  have period : unsigned = value + divisor * (outputCapacity * (extra * multiple)) := by
    rw [whole]; ring1
  rw [period, Int.add_mul_ediv_left _ _ nonzero, Int.add_mul_emod_self_left]

theorem every_subword_shift_factors_the_full_extra_word_capacity_at_the_retained_width
    (count shift : Nat) (bounded : shift < 64) :
    radix64 ^ (count + 1) = 2 ^ shift * (radix64 ^ count * 2 ^ (64 - shift)) := by
  have radix : radix64 = 2 ^ shift * 2 ^ (64 - shift) := by
    change 2 ^ 64 = _
    rw [←Nat.pow_add, show shift + (64 - shift) = 64 by omega]
  calc
    _ = radix64 ^ count * radix64 := Nat.pow_succ _ _
    _ = radix64 ^ count * (2 ^ shift * 2 ^ (64 - shift)) := by rw [radix]
    _ = _ := by ring1

theorem the_entire_source_extraction_chain_derives_the_signed_integer_quotient_residue
    (words : List UInt64) (count shift : Nat) (value : Int)
    (width : words.length = count + 1) (positive : 0 < shift) (bounded : shift < 64)
    (residue : (packWords words : Int) % ((radix64 ^ (count + 1) : Nat) : Int) =
      value % ((radix64 ^ (count + 1) : Nat) : Int)) :
    (packWords (sourceExtractChain shift words).1 : Int) =
      (value / ((2 ^ shift : Nat) : Int)) % ((radix64 ^ count : Nat) : Int) := by
  have extracted := TransferBlstArmInverseExtrChain01.the_entire_original_extraction_chain_has_the_exact_low_word_quotient_residue
    shift words positive bounded
  rw [width, Nat.add_sub_cancel] at extracted
  have cast := congrArg (fun output : Nat => (output : Int)) extracted
  dsimp only at cast
  rw [Int.natCast_emod, Int.natCast_ediv] at cast
  have capacity := every_subword_shift_factors_the_full_extra_word_capacity_at_the_retained_width count shift bounded
  rw [capacity, Nat.cast_mul, Nat.cast_mul] at residue
  have nonzero : ((2 ^ shift : Nat) : Int) ≠ 0 := by
    have positiveNat := Nat.two_pow_pos shift
    exact_mod_cast (Nat.ne_of_gt positiveNat)
  have shifted := a_factored_entire_capacity_derives_the_exact_signed_quotient_residue
    (packWords words : Int) value ((2 ^ shift : Nat) : Int) ((radix64 ^ count : Nat) : Int)
    ((2 ^ (64 - shift) : Nat) : Int) nonzero residue
  exact cast.trans shifted

set_option pp.all true in
#check @equal_entire_residues_derive_an_exact_integer_period_difference
#print axioms equal_entire_residues_derive_an_exact_integer_period_difference
set_option pp.all true in
#check @a_factored_entire_capacity_derives_the_exact_signed_quotient_residue
#print axioms a_factored_entire_capacity_derives_the_exact_signed_quotient_residue
set_option pp.all true in
#check @every_subword_shift_factors_the_full_extra_word_capacity_at_the_retained_width
#print axioms every_subword_shift_factors_the_full_extra_word_capacity_at_the_retained_width
set_option pp.all true in
#check @the_entire_source_extraction_chain_derives_the_signed_integer_quotient_residue
#print axioms the_entire_source_extraction_chain_derives_the_signed_integer_quotient_residue
end ShielddSecurity.TransferBlstArmInverseSignedExtrQuotient01
