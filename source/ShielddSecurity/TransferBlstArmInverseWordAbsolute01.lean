import ShielddSecurity.TransferBlstArmInverseTopWordSign01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordAbsolute01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
attribute [local irreducible] sourceMaskPreparedWords

/-! Exact signed quotient residue plus a derived entire magnitude bound
justifies the source EOR/add-one absolute-value correction. The mask origin
is explicit here, to be supplied by the retained top-word sign theorem. -/

theorem an_exact_signed_residue_and_full_magnitude_bound_derive_the_entire_unsigned_representation
    (unsigned capacity : Nat) (value : Int) (unsignedSmall : unsigned < capacity)
    (magnitudeSmall : value.natAbs < capacity)
    (residue : (unsigned : Int) % (capacity : Int) = value % (capacity : Int)) :
    unsigned = if value < 0 then capacity - value.natAbs else value.natAbs := by
  have unsignedReduced := Int.emod_eq_of_lt (Int.natCast_nonneg unsigned)
    (by exact_mod_cast unsignedSmall : (unsigned : Int) < (capacity : Int))
  rw [unsignedReduced] at residue
  have magnitudeCast : (value.natAbs : Int) < (capacity : Int) := by exact_mod_cast magnitudeSmall
  by_cases negative : value < 0
  · have signed := Int.eq_neg_natAbs_of_nonpos (by omega : value ≤ 0)
    have shiftedNonnegative : 0 ≤ value + (capacity : Int) := by omega
    have shiftedSmall : value + (capacity : Int) < (capacity : Int) := by omega
    have period := Int.add_emod_right value (capacity : Int)
    rw [Int.emod_eq_of_lt shiftedNonnegative shiftedSmall] at period
    rw [←period] at residue
    rw [if_pos negative]
    omega
  · have signed := Int.eq_natAbs_of_nonneg (by omega : 0 ≤ value)
    have valueSmall : value < (capacity : Int) := by omega
    rw [Int.emod_eq_of_lt (by omega) valueSmall] at residue
    rw [if_neg negative]
    omega

theorem exact_signed_quotient_words_and_sign_mask_derive_the_entire_natural_magnitude
    (words : List UInt64) (value : Int) (mask : UInt64)
    (magnitudeSmall : value.natAbs < radix64 ^ words.length)
    (residue : (packWords words : Int) % ((radix64 ^ words.length : Nat) : Int) =
      value % ((radix64 ^ words.length : Nat) : Int))
    (maskOrigin : mask = if value < 0 then (-1 : UInt64) else 0) :
    packWords (sourceMaskPreparedWords words mask).1 = value.natAbs := by
  have representation := an_exact_signed_residue_and_full_magnitude_bound_derive_the_entire_unsigned_representation
    (packWords words) (radix64 ^ words.length) value
    (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words) magnitudeSmall residue
  rw [maskOrigin]
  by_cases negative : value < 0
  · rw [if_pos negative] at representation ⊢
    have nonzero : 0 < packWords words := by omega
    rw [TransferBlstArmInverseSignedWordPrepare01.the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation]
    have negated := (TransferBlstArmInverseWordNegation01.a_nonzero_entire_input_derives_zero_negation_carry_and_the_exact_radix_complement words nonzero).2
    rw [negated]
    omega
  · rw [if_neg negative] at representation ⊢
    rw [(TransferBlstArmInverseSignedWordPrepare01.the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value words).2]
    exact representation

set_option pp.all true in
#check @an_exact_signed_residue_and_full_magnitude_bound_derive_the_entire_unsigned_representation
#print axioms an_exact_signed_residue_and_full_magnitude_bound_derive_the_entire_unsigned_representation
set_option pp.all true in
#check @exact_signed_quotient_words_and_sign_mask_derive_the_entire_natural_magnitude
#print axioms exact_signed_quotient_words_and_sign_mask_derive_the_entire_natural_magnitude
end ShielddSecurity.TransferBlstArmInverseWordAbsolute01
