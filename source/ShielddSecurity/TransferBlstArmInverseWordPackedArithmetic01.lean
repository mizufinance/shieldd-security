import ShielddSecurity.TransferBlstArmInversePackedFactorWords01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordPackedArithmetic01
open TransferBlstArmInversePackedWalk01 (FactorWord)
open TransferBlstArmInversePackedFactorWords01 (sourcePackedRegisterWord)
attribute [local irreducible] sourcePackedRegisterWord

/-! Exact UInt64 codec for the source modulo64 packed factor arithmetic.
All operations are entire-word modular operations, without signed slot
assumptions. The source loop control and compiled ISA are separate. -/

local instance packedModulusNonzero : NeZero (18446744073709551616 : Nat) := ⟨by decide⟩

theorem entire_modulo64_packed_register_addition_is_exact_uint64_word_addition
    (left right : FactorWord) :
    sourcePackedRegisterWord (left + right) = sourcePackedRegisterWord left + sourcePackedRegisterWord right := by
  unfold sourcePackedRegisterWord
  rw [ZMod.val_add, UInt64.ofNat_mod_size, UInt64.ofNat_add]

theorem entire_modulo64_packed_register_negation_is_exact_uint64_word_negation
    (word : FactorWord) : sourcePackedRegisterWord (-word) = -sourcePackedRegisterWord word := by
  apply UInt64.toNat_inj.mp
  simp only [TransferBlstArmInversePackedFactorWords01.the_entire_source_packed_register_is_preserved_by_its_uint64_conversion,
    UInt64.toNat_neg, ZMod.neg_val']

theorem entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction
    (left right : FactorWord) :
    sourcePackedRegisterWord (left - right) = sourcePackedRegisterWord left - sourcePackedRegisterWord right := by
  rw [sub_eq_add_neg, entire_modulo64_packed_register_addition_is_exact_uint64_word_addition,
    entire_modulo64_packed_register_negation_is_exact_uint64_word_negation, UInt64.sub_eq_add_neg]

theorem every_natural_packed_register_constant_has_its_exact_uint64_modular_code
    (value : Nat) : sourcePackedRegisterWord (value : FactorWord) = UInt64.ofNat value := by
  unfold sourcePackedRegisterWord
  rw [ZMod.val_natCast, UInt64.ofNat_mod_size]

theorem original_biased_pair_constant_has_the_exact_entire_uint64_word_code :
    sourcePackedRegisterWord (TransferBlstArmInversePack01.sourceBiasPair : FactorWord) = 9223372034707292159 := by
  unfold sourcePackedRegisterWord TransferBlstArmInversePack01.sourceBiasPair
  decide +kernel

set_option pp.all true in
#check @packedModulusNonzero
#print axioms packedModulusNonzero
set_option pp.all true in
#check @entire_modulo64_packed_register_addition_is_exact_uint64_word_addition
#print axioms entire_modulo64_packed_register_addition_is_exact_uint64_word_addition
set_option pp.all true in
#check @entire_modulo64_packed_register_negation_is_exact_uint64_word_negation
#print axioms entire_modulo64_packed_register_negation_is_exact_uint64_word_negation
set_option pp.all true in
#check @entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction
#print axioms entire_modulo64_packed_register_subtraction_is_exact_uint64_word_subtraction
set_option pp.all true in
#check @every_natural_packed_register_constant_has_its_exact_uint64_modular_code
#print axioms every_natural_packed_register_constant_has_its_exact_uint64_modular_code
set_option pp.all true in
#check @original_biased_pair_constant_has_the_exact_entire_uint64_word_code
#print axioms original_biased_pair_constant_has_the_exact_entire_uint64_word_code
end ShielddSecurity.TransferBlstArmInverseWordPackedArithmetic01
