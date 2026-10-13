import ShielddSecurity.TransferBlstArmInverseSign01
import ShielddSecurity.TransferBlstArmInverseTail01
import ShielddSecurity.TransferBlstArmAdd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFirst01
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmAdd01 (sourceArmAddRaw)
open TransferBlstArmInverseSign01 (sourceRx2 sourceWideRadix sourceCorrectionShift sourceSignedFirst)

/-! Original first signed adjustment keeps the low four words, adds rx2 to
the high four words when the extra signed top is negative, and threads the
actual captured addition carry into that top. Full signed value and sign
guard are derived from word carry conservation. Coefficient production,
the second word adjustment and actual native ISA/ABI remain separate. -/

abbrev WideState := Vector UInt64 4 × Vector UInt64 4 × Int

theorem symbolic_word_append_has_the_entire_radix_weighted_value (low high : List UInt64) :
    packWords (low++high)=packWords low+radix64^low.length*packWords high := by
  induction low with
  | nil => simp only [List.nil_append,packWords,List.length_nil,pow_zero,one_mul,zero_add]
  | cons word rest ih =>
      rw [List.cons_append,packWords,ih,packWords,List.length_cons,pow_succ]
      ring

def sourceWideRaw (s : WideState) : Nat := packWords (s.1.toList++s.2.1.toList)
def sourceWideMeaning (s : WideState) : Int := (sourceWideRaw s:Int)+sourceWideRadix*s.2.2
def sourceFourRadix : Int := ((radix64^4:Nat):Int)

theorem original_two_four_word_halves_derive_the_unsigned_wide_range (s : WideState) :
    0≤(sourceWideRaw s:Int) ∧ (sourceWideRaw s:Int)<sourceWideRadix := by
  have range := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (s.1.toList++s.2.1.toList)
  rw [List.length_append,Vector.length_toList,Vector.length_toList] at range
  refine ⟨Int.natCast_nonneg _,?_⟩
  change (packWords (s.1.toList++s.2.1.toList):Int)<((radix64^8:Nat):Int)
  exact_mod_cast range

theorem original_extra_top_sign_is_the_entire_signed_wide_value_sign (s : WideState) :
    s.2.2<0 ↔ sourceWideMeaning s<0 := by
  have range := original_two_four_word_halves_derive_the_unsigned_wide_range s
  have positive : 0<sourceWideRadix := by decide
  constructor
  · intro negative
    have topBound : s.2.2≤-1 := by omega
    have productBound := mul_le_mul_of_nonneg_left topBound (le_of_lt positive)
    simp only [mul_neg,mul_one] at productBound
    unfold sourceWideMeaning
    omega
  · intro negative
    by_contra absent
    have topNonnegative : 0≤s.2.2 := by omega
    have productNonnegative := mul_nonneg (le_of_lt positive) topNonnegative
    unfold sourceWideMeaning at negative
    omega

def sourceAddedHigh (high : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceArmAddRaw high sourceRx2).1.toArray,by
    rw [List.size_toArray,TransferBlstArmAdd01.source_arm_add_raw_retains_four_limbs]⟩

theorem original_high_add_vector_retains_every_source_addition_word (high : Vector UInt64 4) :
    (sourceAddedHigh high).toList=(sourceArmAddRaw high sourceRx2).1 := by
  simp only [sourceAddedHigh,Vector.toList,List.toList_toArray]

theorem original_high_addition_threads_its_actual_four_word_carry (high : Vector UInt64 4) :
    (packWords (sourceAddedHigh high).toList:Int)+sourceFourRadix*((sourceArmAddRaw high sourceRx2).2.toNat:Int)=
      (packWords high.toList:Int)+(packWords sourceRx2.toList:Int) := by
  have leftProjection : high.toList.length≤sourceRx2.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have rightProjection : sourceRx2.toList.length≤high.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (high.toList.zip sourceRx2.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,List.length_zip,
    Vector.length_toList,Vector.length_toList,Nat.min_self] at conserved
  change packWords (sourceArmAddRaw high sourceRx2).1+radix64^4*(sourceArmAddRaw high sourceRx2).2.toNat=
    packWords high.toList+packWords sourceRx2.toList+0 at conserved
  rw [Nat.add_zero] at conserved
  rw [original_high_add_vector_retains_every_source_addition_word,sourceFourRadix]
  exact_mod_cast conserved

theorem original_wide_radix_is_the_square_of_the_four_word_radix :
    sourceWideRadix=sourceFourRadix*sourceFourRadix := by decide

def sourceFirstAddedState (s : WideState) : WideState :=
  (s.1,sourceAddedHigh s.2.1,s.2.2+((sourceArmAddRaw s.2.1 sourceRx2).2.toNat:Int))

theorem original_first_high_word_addition_derives_the_entire_signed_integer_adjustment (s : WideState) :
    sourceWideMeaning (sourceFirstAddedState s)=sourceWideMeaning s+sourceCorrectionShift := by
  have carry := original_high_addition_threads_its_actual_four_word_carry s.2.1
  simp only [sourceWideMeaning,sourceWideRaw,sourceFirstAddedState,
    symbolic_word_append_has_the_entire_radix_weighted_value,Vector.length_toList,Nat.cast_add,Nat.cast_mul]
  change (packWords s.1.toList:Int)+sourceFourRadix*(packWords (sourceAddedHigh s.2.1).toList:Int)+
    sourceWideRadix*(s.2.2+((sourceArmAddRaw s.2.1 sourceRx2).2.toNat:Int))=
      (packWords s.1.toList:Int)+sourceFourRadix*(packWords s.2.1.toList:Int)+sourceWideRadix*s.2.2+sourceCorrectionShift
  calc
    _ = (packWords s.1.toList:Int)+sourceFourRadix*((packWords (sourceAddedHigh s.2.1).toList:Int)+
      sourceFourRadix*((sourceArmAddRaw s.2.1 sourceRx2).2.toNat:Int))+sourceWideRadix*s.2.2 := by
        rw [original_wide_radix_is_the_square_of_the_four_word_radix]
        ring
    _ = (packWords s.1.toList:Int)+sourceFourRadix*((packWords s.2.1.toList:Int)+(packWords sourceRx2.toList:Int))+
      sourceWideRadix*s.2.2 := by rw [carry]
    _ = _ := by rw [sourceCorrectionShift]; change _ = _ + (packWords sourceRx2.toList:Int)*sourceFourRadix; ring

def sourceFirstWordCorrection (s : WideState) : WideState :=
  if s.2.2<0 then sourceFirstAddedState s else s

theorem original_first_signed_word_correction_is_the_qualified_signed_integer_correction (s : WideState) :
    sourceWideMeaning (sourceFirstWordCorrection s)=sourceSignedFirst (sourceWideMeaning s) := by
  rw [sourceFirstWordCorrection,sourceSignedFirst]
  by_cases negative : s.2.2<0
  · have fullNegative := (original_extra_top_sign_is_the_entire_signed_wide_value_sign s).mp negative
    rw [if_pos negative,if_pos fullNegative,original_first_high_word_addition_derives_the_entire_signed_integer_adjustment]
  · have fullNonnegative : ¬sourceWideMeaning s<0 := fun impossible => negative
      ((original_extra_top_sign_is_the_entire_signed_wide_value_sign s).mpr impossible)
    rw [if_neg negative,if_neg fullNonnegative]

set_option pp.all true in
#check @WideState
#print axioms WideState
set_option pp.all true in
#check @symbolic_word_append_has_the_entire_radix_weighted_value
#print axioms symbolic_word_append_has_the_entire_radix_weighted_value
set_option pp.all true in
#check @sourceWideRaw
#print axioms sourceWideRaw
set_option pp.all true in
#check @sourceWideMeaning
#print axioms sourceWideMeaning
set_option pp.all true in
#check @sourceFourRadix
#print axioms sourceFourRadix
set_option pp.all true in
#check @original_two_four_word_halves_derive_the_unsigned_wide_range
#print axioms original_two_four_word_halves_derive_the_unsigned_wide_range
set_option pp.all true in
#check @original_extra_top_sign_is_the_entire_signed_wide_value_sign
#print axioms original_extra_top_sign_is_the_entire_signed_wide_value_sign
set_option pp.all true in
#check @sourceAddedHigh
#print axioms sourceAddedHigh
set_option pp.all true in
#check @original_high_add_vector_retains_every_source_addition_word
#print axioms original_high_add_vector_retains_every_source_addition_word
set_option pp.all true in
#check @original_high_addition_threads_its_actual_four_word_carry
#print axioms original_high_addition_threads_its_actual_four_word_carry
set_option pp.all true in
#check @original_wide_radix_is_the_square_of_the_four_word_radix
#print axioms original_wide_radix_is_the_square_of_the_four_word_radix
set_option pp.all true in
#check @sourceFirstAddedState
#print axioms sourceFirstAddedState
set_option pp.all true in
#check @original_first_high_word_addition_derives_the_entire_signed_integer_adjustment
#print axioms original_first_high_word_addition_derives_the_entire_signed_integer_adjustment
set_option pp.all true in
#check @sourceFirstWordCorrection
#print axioms sourceFirstWordCorrection
set_option pp.all true in
#check @original_first_signed_word_correction_is_the_qualified_signed_integer_correction
#print axioms original_first_signed_word_correction_is_the_qualified_signed_integer_correction
end ShielddSecurity.TransferBlstArmInverseFirst01
