import ShielddSecurity.TransferBlstArmCiosStep01
import ShielddSecurity.TransferScalarFieldValues01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCiosWalk01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmCiosStep01
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceCiosStep sourceMulStepInput sourceMulStepWords
  TransferBlstArmMulRows01.sourceMulAddRows
  TransferBlstArmFiveReduction01.sourceFiveFirstPass TransferBlstArmFiveReduction01.sourceFiveSecondPass

def sourceCiosWalk (operand : CanonicalScalar) : List UInt64 → SourceIntermediate → SourceIntermediate
  | [], accumulator => accumulator
  | digit::rest, accumulator => sourceCiosWalk operand rest (sourceCiosStep operand accumulator digit)

theorem symbolic_original_cios_walk_derives_the_entire_radix_weighted_product_relation
    (operand : CanonicalScalar) (digits : List UInt64) (accumulator : SourceIntermediate) :
    (radix64^digits.length*packWords (sourceCiosWalk operand digits accumulator).val.toList)%nullifierModulus =
      (packWords accumulator.val.toList+packWords operand.words.toList*packWords digits)%nullifierModulus := by
  induction digits generalizing accumulator with
  | nil => simp only [sourceCiosWalk,List.length_nil,Nat.pow_zero,Nat.one_mul,packWords,Nat.mul_zero,Nat.add_zero]
  | cons digit rest ih =>
    let next := sourceCiosStep operand accumulator digit
    have tail := ih next
    have scaled := congrArg (fun value : Nat => radix64*value%nullifierModulus) tail
    simp only [Nat.mul_mod_mod] at scaled
    have step := original_cios_step_derives_the_full_scaled_integer_from_the_original_input operand accumulator digit
    have interpreted : radix64*(packWords next.val.toList+packWords operand.words.toList*packWords rest) =
        (packWords accumulator.val.toList+packWords operand.words.toList*packWords (digit::rest))+
          nullifierModulus*(TransferBlstArmCancellation01.sourceArmMultiplier
            ((sourceMulStepInput operand.words accumulator.val digit).headD 0)).toNat := by
      rw [Nat.mul_add,step,packWords]
      ring
    rw [interpreted,Nat.add_mul_mod_self_left] at scaled
    simpa only [sourceCiosWalk,List.length_cons,Nat.pow_succ',Nat.mul_assoc] using scaled

def sourceCiosZero : SourceIntermediate :=
  ⟨#v[0,0,0,0],by decide⟩

theorem original_cios_zero_has_zero_packed_input : packWords sourceCiosZero.val.toList=0 := by
  rfl

theorem actual_four_original_cios_blocks_derive_the_full_input_product_relation
    (operand : CanonicalScalar) (digits : Vector UInt64 4) :
    (radix64^4*packWords (sourceCiosWalk operand digits.toList sourceCiosZero).val.toList)%nullifierModulus =
      (packWords operand.words.toList*packWords digits.toList)%nullifierModulus := by
  have relation := symbolic_original_cios_walk_derives_the_entire_radix_weighted_product_relation
    operand digits.toList sourceCiosZero
  simpa only [Vector.length_toList,original_cios_zero_has_zero_packed_input,Nat.zero_add] using relation

/-- The final assembly SBCS includes the fifth word. Each typed step has
already derived its zero overflow; its remaining borrow therefore selects
the same four words as the qualified low-only borrow selector. -/
def sourceCiosFinalWords (words : Vector UInt64 4) : List UInt64 :=
  let difference := TransferScalarBorrowWalk01.borrowWalk false
    (words.toList.zip TransferScalarFourRoundWrapper01.modulusWords)
  let finalBorrow := TransferScalarBorrowWalk01.nextBorrow 0 0 difference.2
  if finalBorrow then words.toList else difference.1

theorem actual_final_cios_zero_high_word_comparison_derives_the_qualified_borrow_selector
    (words : Vector UInt64 4) :
    sourceCiosFinalWords words = TransferBlstArmNormalized01.sourceArmBorrowSelect words.toList := by
  have lowBorrow : ∀ borrow : Bool, TransferScalarBorrowWalk01.nextBorrow 0 0 borrow = borrow := by
    intro borrow
    cases borrow <;> simp [TransferScalarBorrowWalk01.nextBorrow,TransferScalarSbbPrimitive01.borrowBit]
  rw [sourceCiosFinalWords,lowBorrow]
  rfl

theorem actual_final_original_cios_output_derives_canonical_width_and_range
    (operand : CanonicalScalar) (digits : Vector UInt64 4) :
    (sourceCiosFinalWords (sourceCiosWalk operand digits.toList sourceCiosZero).val).length=4 ∧
      packWords (sourceCiosFinalWords (sourceCiosWalk operand digits.toList sourceCiosZero).val) < nullifierModulus := by
  rw [actual_final_cios_zero_high_word_comparison_derives_the_qualified_borrow_selector]
  constructor
  · exact TransferBlstArmNormalized01.actual_final_borrow_select_retains_the_four_word_width _ Vector.length_toList
  · rw [TransferBlstArmNormalized01.actual_final_borrow_select_derives_exact_single_modulus_normalization _ Vector.length_toList]
    exact TransferScalarWideReduction01.single_subtraction_of_value_below_twice_modulus_is_canonical
      _ (sourceCiosWalk operand digits.toList sourceCiosZero).property

def sourceCiosProduct (operand : CanonicalScalar) (digits : Vector UInt64 4) : CanonicalScalar :=
  let output := sourceCiosFinalWords (sourceCiosWalk operand digits.toList sourceCiosZero).val
  let contract := actual_final_original_cios_output_derives_canonical_width_and_range operand digits
  TransferScalarProgramInvariant01.certifyResult output contract.1 contract.2

theorem original_cios_product_fixed_vector_is_the_actual_selected_words
    (operand : CanonicalScalar) (digits : Vector UInt64 4) :
    (sourceCiosProduct operand digits).words.toList =
      sourceCiosFinalWords (sourceCiosWalk operand digits.toList sourceCiosZero).val := by
  simp only [sourceCiosProduct,TransferScalarProgramInvariant01.certifyResult,Vector.toList,List.toList_toArray]

theorem actual_original_four_block_product_and_final_selector_derive_the_montgomery_contract
    (operand : CanonicalScalar) (digits : Vector UInt64 4) :
    (radix64^4*packWords (sourceCiosProduct operand digits).words.toList)%nullifierModulus =
      (packWords operand.words.toList*packWords digits.toList)%nullifierModulus := by
  have normalization : packWords (sourceCiosProduct operand digits).words.toList%nullifierModulus =
      packWords (sourceCiosWalk operand digits.toList sourceCiosZero).val.toList%nullifierModulus := by
    rw [original_cios_product_fixed_vector_is_the_actual_selected_words,
      actual_final_cios_zero_high_word_comparison_derives_the_qualified_borrow_selector,
      TransferBlstArmNormalized01.actual_final_borrow_select_derives_exact_single_modulus_normalization _ Vector.length_toList]
    exact TransferScalarMontgomeryValue01.single_modulus_normalization_preserves_modular_value _
  have weighted := congrArg (fun value : Nat => radix64^4*value%nullifierModulus) normalization
  simp only [Nat.mul_mod_mod] at weighted
  exact weighted.trans (actual_four_original_cios_blocks_derive_the_full_input_product_relation operand digits)

theorem actual_original_cios_program_derives_the_two_original_input_field_values_product
    (operand : CanonicalScalar) (digits : Vector UInt64 4) :
    TransferBlstArmNormalized01.sourceBlstFrWordMeaning (sourceCiosProduct operand digits).words =
      TransferBlstArmNormalized01.sourceBlstFrWordMeaning operand.words *
        TransferBlstArmNormalized01.sourceBlstFrWordMeaning digits := by
  have relation := actual_original_four_block_product_and_final_selector_derive_the_montgomery_contract operand digits
  have meaning := TransferScalarFieldValues01.canonical_montgomery_word_contract_derives_exact_field_product
    (packWords operand.words.toList) (packWords digits.toList)
    (packWords (sourceCiosProduct operand digits).words.toList) (sourceCiosProduct operand digits).canonical relation
  change (TransferScalarMontgomeryValue01.montgomeryValue (sourceCiosProduct operand digits).words : ZMod nullifierModulus) =
    (TransferScalarMontgomeryValue01.montgomeryValue operand.words : ZMod nullifierModulus) *
      (TransferScalarMontgomeryValue01.montgomeryValue digits : ZMod nullifierModulus)
  change TransferScalarMontgomeryValue01.montgomeryValue (sourceCiosProduct operand digits).words =
    (TransferScalarMontgomeryValue01.montgomeryValue operand.words*TransferScalarMontgomeryValue01.montgomeryValue digits)%nullifierModulus at meaning
  rw [meaning,ZMod.natCast_mod,Nat.cast_mul]
set_option pp.all true in
#check @sourceCiosWalk
#print axioms sourceCiosWalk
set_option pp.all true in
#check @symbolic_original_cios_walk_derives_the_entire_radix_weighted_product_relation
#print axioms symbolic_original_cios_walk_derives_the_entire_radix_weighted_product_relation
set_option pp.all true in
#check @sourceCiosZero
#print axioms sourceCiosZero
set_option pp.all true in
#check @original_cios_zero_has_zero_packed_input
#print axioms original_cios_zero_has_zero_packed_input
set_option pp.all true in
#check @actual_four_original_cios_blocks_derive_the_full_input_product_relation
#print axioms actual_four_original_cios_blocks_derive_the_full_input_product_relation
set_option pp.all true in
#check @sourceCiosFinalWords
#print axioms sourceCiosFinalWords
set_option pp.all true in
#check @actual_final_cios_zero_high_word_comparison_derives_the_qualified_borrow_selector
#print axioms actual_final_cios_zero_high_word_comparison_derives_the_qualified_borrow_selector
set_option pp.all true in
#check @actual_final_original_cios_output_derives_canonical_width_and_range
#print axioms actual_final_original_cios_output_derives_canonical_width_and_range
set_option pp.all true in
#check @sourceCiosProduct
#print axioms sourceCiosProduct
set_option pp.all true in
#check @original_cios_product_fixed_vector_is_the_actual_selected_words
#print axioms original_cios_product_fixed_vector_is_the_actual_selected_words
set_option pp.all true in
#check @actual_original_four_block_product_and_final_selector_derive_the_montgomery_contract
#print axioms actual_original_four_block_product_and_final_selector_derive_the_montgomery_contract
set_option pp.all true in
#check @actual_original_cios_program_derives_the_two_original_input_field_values_product
#print axioms actual_original_cios_program_derives_the_two_original_input_field_values_product
end ShielddSecurity.TransferBlstArmCiosWalk01
