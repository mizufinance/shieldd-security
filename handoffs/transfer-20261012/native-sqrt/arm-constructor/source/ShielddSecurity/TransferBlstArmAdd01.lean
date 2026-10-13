import ShielddSecurity.TransferBlstArmCneg01
import ShielddSecurity.TransferBlstArmCarryChains01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmAdd01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferScalarBorrowWalk01 (borrowWalk nextBorrow)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBlstArmNormalized01 (sourceArmBorrowSelect sourceBlstFrWordMeaning)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceAddCarryChain borrowWalk
  TransferScalarCanonicalAdd01.adcLoop TransferScalarCanonicalAdd01.sourceAddWords

def sourceArmAddRaw (left right : Vector UInt64 4) : List UInt64 × Bool :=
  sourceAddCarryChain false (left.toList.zip right.toList)

theorem source_arm_add_raw_retains_four_limbs (left right : Vector UInt64 4) :
    (sourceArmAddRaw left right).1.length = 4 := by
  rw [sourceArmAddRaw,TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip,Vector.length_toList,Vector.length_toList,Nat.min_self]

theorem canonical_inputs_derive_actual_arm_add_zero_overflow_and_exact_integer_sum
    (left right : CanonicalScalar) :
    (sourceArmAddRaw left.words right.words).2 = false ∧
      packWords (sourceArmAddRaw left.words right.words).1 =
        packWords left.words.toList + packWords right.words.toList := by
  have leftProjection : left.words.toList.length ≤ right.words.toList.length := by
    rw [Vector.length_toList,Vector.length_toList]
  have rightProjection : right.words.toList.length ≤ left.words.toList.length := by
    rw [Vector.length_toList,Vector.length_toList]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (left.words.toList.zip right.words.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,List.length_zip,
    Vector.length_toList,Vector.length_toList,Nat.min_self] at conserved
  change packWords (sourceArmAddRaw left.words right.words).1 +
    radix64^4*(sourceArmAddRaw left.words right.words).2.toNat =
      packWords left.words.toList + packWords right.words.toList + 0 at conserved
  have sumBound : packWords left.words.toList + packWords right.words.toList < radix64^4 := by
    have l := left.canonical
    have r := right.canonical
    have radixBound := TransferScalarWideReduction01.twice_actual_modulus_fits_four_word_radix
    omega
  have zeroFlag : (sourceArmAddRaw left.words right.words).2 = false := by
    cases flag : (sourceArmAddRaw left.words right.words).2 with
    | false => rfl
    | true => rw [flag] at conserved; change _ + radix64^4*1 = _ + 0 at conserved; omega
  rw [zeroFlag] at conserved
  change packWords (sourceArmAddRaw left.words right.words).1 + radix64^4*0 =
    packWords left.words.toList + packWords right.words.toList + 0 at conserved
  simp only [Nat.mul_zero,Nat.add_zero] at conserved
  exact ⟨zeroFlag,conserved⟩

/-- Locked add_mod_256 arithmetic, including the fifth SBCS which subtracts
the low-chain borrow from the captured ADCS overflow before CSEL. Native
register flags, pointers and compiler execution remain separate obligations. -/
def sourceArmAddWords (left right : Vector UInt64 4) : List UInt64 :=
  let sum := sourceArmAddRaw left right
  let difference := borrowWalk false (sum.1.zip modulusWords)
  let finalBorrow := nextBorrow (UInt64.ofNat sum.2.toNat) 0 difference.2
  if finalBorrow then sum.1 else difference.1

theorem actual_fifth_subtraction_with_zero_overflow_retains_exact_low_borrow (borrow : Bool) :
    nextBorrow (UInt64.ofNat (0 : Nat)) 0 borrow = borrow := by
  cases borrow <;> simp [nextBorrow,TransferScalarSbbPrimitive01.borrowBit]

theorem canonical_actual_arm_add_derives_every_qualified_sdk_output_word
    (left right : CanonicalScalar) :
    sourceArmAddWords left.words right.words = TransferScalarCanonicalAdd01.sourceAddWords left.words right.words := by
  obtain ⟨noOverflow,rawSum⟩ := canonical_inputs_derive_actual_arm_add_zero_overflow_and_exact_integer_sum left right
  have selected : sourceArmAddWords left.words right.words =
      sourceArmBorrowSelect (sourceArmAddRaw left.words right.words).1 := by
    rw [sourceArmAddWords,noOverflow]
    change (if nextBorrow (UInt64.ofNat (0 : Nat)) 0
      (borrowWalk false ((sourceArmAddRaw left.words right.words).1.zip modulusWords)).2 then
        (sourceArmAddRaw left.words right.words).1 else
        (borrowWalk false ((sourceArmAddRaw left.words right.words).1.zip modulusWords)).1) = _
    rw [actual_fifth_subtraction_with_zero_overflow_retains_exact_low_borrow]
    rfl
  obtain ⟨oldWidth,_,oldSum⟩ :=
    TransferScalarCanonicalAdd01.canonical_operands_derive_four_adc_limbs_zero_carry_and_exact_sum left right
  have sameRaw := TransferCanonicalWordEquality01.equal_width_packed_u64_lists_are_equal
    (sourceArmAddRaw left.words right.words).1
    (TransferScalarCanonicalAdd01.adcLoop 0 (left.words.toList.zip right.words.toList)).1
    ((source_arm_add_raw_retains_four_limbs _ _).trans oldWidth.symm) (rawSum.trans oldSum.symm)
  rw [selected,TransferBlstArmNormalized01.actual_final_borrow_select_derives_the_qualified_normalized_word_vector
    _ (source_arm_add_raw_retains_four_limbs _ _),sameRaw,TransferScalarCanonicalAdd01.sourceAddWords]

theorem canonical_actual_arm_add_derives_width_range_and_modular_sum (left right : CanonicalScalar) :
    (sourceArmAddWords left.words right.words).length = 4 ∧
      packWords (sourceArmAddWords left.words right.words) < nullifierModulus ∧
      packWords (sourceArmAddWords left.words right.words) =
        (packWords left.words.toList + packWords right.words.toList) % nullifierModulus := by
  rw [canonical_actual_arm_add_derives_every_qualified_sdk_output_word]
  exact TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum left right

def sourceArmAdd (left right : CanonicalScalar) : CanonicalScalar :=
  let contract := canonical_actual_arm_add_derives_width_range_and_modular_sum left right
  TransferScalarProgramInvariant01.certifyResult (sourceArmAddWords left.words right.words) contract.1 contract.2.1

theorem canonical_actual_arm_add_derives_the_original_input_field_sum (left right : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceArmAdd left right).words =
      sourceBlstFrWordMeaning left.words + sourceBlstFrWordMeaning right.words := by
  have output : packWords (sourceArmAdd left right).words.toList =
      (packWords left.words.toList + packWords right.words.toList) % nullifierModulus := by
    change packWords (sourceArmAddWords left.words right.words).toArray.toList = _
    rw [List.toList_toArray]
    exact (canonical_actual_arm_add_derives_width_range_and_modular_sum left right).2.2
  rw [TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue,output,
    ZMod.natCast_mod,Nat.cast_add,mul_add,
    ← TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue,
    ← TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue]
set_option pp.all true in
#check @sourceArmAddRaw
#print axioms sourceArmAddRaw
set_option pp.all true in
#check @source_arm_add_raw_retains_four_limbs
#print axioms source_arm_add_raw_retains_four_limbs
set_option pp.all true in
#check @canonical_inputs_derive_actual_arm_add_zero_overflow_and_exact_integer_sum
#print axioms canonical_inputs_derive_actual_arm_add_zero_overflow_and_exact_integer_sum
set_option pp.all true in
#check @sourceArmAddWords
#print axioms sourceArmAddWords
set_option pp.all true in
#check @actual_fifth_subtraction_with_zero_overflow_retains_exact_low_borrow
#print axioms actual_fifth_subtraction_with_zero_overflow_retains_exact_low_borrow
set_option pp.all true in
#check @canonical_actual_arm_add_derives_every_qualified_sdk_output_word
#print axioms canonical_actual_arm_add_derives_every_qualified_sdk_output_word
set_option pp.all true in
#check @canonical_actual_arm_add_derives_width_range_and_modular_sum
#print axioms canonical_actual_arm_add_derives_width_range_and_modular_sum
set_option pp.all true in
#check @sourceArmAdd
#print axioms sourceArmAdd
set_option pp.all true in
#check @canonical_actual_arm_add_derives_the_original_input_field_sum
#print axioms canonical_actual_arm_add_derives_the_original_input_field_sum
end ShielddSecurity.TransferBlstArmAdd01
