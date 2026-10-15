import ShielddSecurity.TransferBlstArmInverseSign01
import ShielddSecurity.TransferBlstArmAddRaw01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMask01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSign01 (sourceRx2)

/-! Word interpretation of the original second correction's NEG/OR excess
mask, ASR sign mask, EOR and ADD/ADC two's-complement operand. Exact original
rx2 words and carry-chain operations are used. The required extra-top range
is explicit; production of that top, final high addition and native execution
remain separate. -/

def sourceTopCode (top : Int) : UInt64 := UInt64.ofNat ((top%(radix64:Int)).toNat)
def sourceExcessMask (top : Int) : UInt64 := sourceTopCode top ||| sourceTopCode (-top)
def sourceNegationMask (top : Int) : UInt64 :=
  if (2^63:Nat)≤(sourceTopCode (-top)).toNat then UInt64.ofNat (radix64-1) else 0

def sourceSelectedWords (top : Int) : Vector UInt64 4 :=
  sourceRx2.map (fun word => (word &&& sourceExcessMask top) ^^^ sourceNegationMask top)

def sourceOperandCarry (top : Int) : Bool :=
  decide (((sourceNegationMask top >>> 63).toNat)=1)

def sourceOperandWords (top : Int) : List UInt64 :=
  (TransferBlstArmCarryChains01.sourceAddCarryChain (sourceOperandCarry top)
    ((sourceSelectedWords top).toList.zip (Vector.replicate 4 (0:UInt64)).toList)).1

theorem original_second_correction_operand_retains_four_words (top : Int) :
    (sourceOperandWords top).length=4 := by
  rw [sourceOperandWords,TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip,Vector.length_toList,Vector.length_toList,Nat.min_self]

def sourceOperandVector (top : Int) : Vector UInt64 4 :=
  ⟨(sourceOperandWords top).toArray,by rw [List.size_toArray,original_second_correction_operand_retains_four_words]⟩

theorem original_second_correction_vector_retains_the_actual_operand_words (top : Int) :
    (sourceOperandVector top).toList=sourceOperandWords top := by
  simp only [sourceOperandVector,Vector.toList,List.toList_toArray]

theorem original_second_correction_masks_derive_the_actual_selected_operand_value
    (top : Int) (lower : -1≤top) (upper : top≤1) :
    packWords (sourceOperandVector top).toList =
      if top<0 then packWords sourceRx2.toList
      else if 0<top then radix64^4-packWords sourceRx2.toList else 0 := by
  have alternatives : top=-1 ∨ top=0 ∨ top=1 := by omega
  rcases alternatives with negative | zero | positive
  · subst top
    rw [original_second_correction_vector_retains_the_actual_operand_words]
    decide +kernel
  · subst top
    rw [original_second_correction_vector_retains_the_actual_operand_words]
    decide +kernel
  · subst top
    rw [original_second_correction_vector_retains_the_actual_operand_words]
    decide +kernel

set_option pp.all true in
#check @sourceTopCode
#print axioms sourceTopCode
set_option pp.all true in
#check @sourceExcessMask
#print axioms sourceExcessMask
set_option pp.all true in
#check @sourceNegationMask
#print axioms sourceNegationMask
set_option pp.all true in
#check @sourceSelectedWords
#print axioms sourceSelectedWords
set_option pp.all true in
#check @sourceOperandCarry
#print axioms sourceOperandCarry
set_option pp.all true in
#check @sourceOperandWords
#print axioms sourceOperandWords
set_option pp.all true in
#check @original_second_correction_operand_retains_four_words
#print axioms original_second_correction_operand_retains_four_words
set_option pp.all true in
#check @sourceOperandVector
#print axioms sourceOperandVector
set_option pp.all true in
#check @original_second_correction_vector_retains_the_actual_operand_words
#print axioms original_second_correction_vector_retains_the_actual_operand_words
set_option pp.all true in
#check @original_second_correction_masks_derive_the_actual_selected_operand_value
#print axioms original_second_correction_masks_derive_the_actual_selected_operand_value
end ShielddSecurity.TransferBlstArmInverseMask01
