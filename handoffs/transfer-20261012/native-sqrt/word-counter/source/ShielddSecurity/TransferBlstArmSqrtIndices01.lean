import ShielddSecurity.TransferBlstArmSqrtWhile01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtIndices01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmRingCaller01 (sourceCallerOne sourceCallerSquare)
attribute [local irreducible] sourceCallerOne sourceCallerSquare
local instance scalarPrimeFact : Fact (Nat.Prime TransferBoundedNativeCodec01.nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero TransferBoundedNativeCodec01.nullifierModulus := ⟨by decide⟩

/-! Explicit UInt32 search counter and correction subtraction refine the
natural-number recurrence within the original 32-step domain. Square occurs
before increment and refusal in the source counter recurrence. Compiler/ISA
and inverse completeness remain separate. -/

def sourceUInt32SearchWalk (m : UInt32) : Nat → UInt32 → CanonicalScalar → Option Nat
  | 0,_,_ => none
  | fuel+1,index,value =>
      if value.words = sourceCallerOne.words then some index.toNat
      else
        let next := sourceCallerSquare value
        let nextIndex := index+1
        if nextIndex=m then none else sourceUInt32SearchWalk m fuel nextIndex next

theorem original_small_index_word_encoding_is_injective
    (left right : Nat) (leftBound : left ≤ 32) (rightBound : right ≤ 32) :
    UInt32.ofNat left = UInt32.ofNat right ↔ left=right := by
  constructor
  · intro same
    have values := congrArg UInt32.toNat same
    have leftFits : left < UInt32.size := by change left < 4294967296; omega
    have rightFits : right < UInt32.size := by change right < 4294967296; omega
    simpa only [UInt32.toNat_ofNat_of_lt' leftFits,UInt32.toNat_ofNat_of_lt' rightFits] using values
  · intro same; rw [same]

theorem complete_original_uint32_search_counter_is_the_qualified_original_word_search
    (m fuel index : Nat) (value : CanonicalScalar) (inside : index<m) (bounded : m≤32) :
    sourceUInt32SearchWalk (UInt32.ofNat m) fuel (UInt32.ofNat index) value =
      TransferBlstArmSqrtSearch01.sourceWordSearchWalk m fuel index value := by
  induction fuel generalizing index value with
  | zero => rfl
  | succ fuel ih =>
      rw [sourceUInt32SearchWalk,TransferBlstArmSqrtSearch01.sourceWordSearchWalk]
      by_cases unit : value.words = sourceCallerOne.words
      · simp only [if_pos unit]
        have fits : index < UInt32.size := by change index < 4294967296; omega
        rw [UInt32.toNat_ofNat_of_lt' fits]
      · simp only [if_neg unit]
        have increment : (UInt32.ofNat index)+1 = UInt32.ofNat (index+1) := by
          exact (UInt32.ofNat_add index 1).symm
        rw [increment]
        have guard := original_small_index_word_encoding_is_injective (index+1) m (by omega) bounded
        by_cases boundary : index+1=m
        · have wordBoundary := guard.mpr boundary
          simp only [if_pos boundary,if_pos wordBoundary]
        · have wordNonboundary : UInt32.ofNat (index+1) ≠ UInt32.ofNat m := fun same => boundary (guard.mp same)
          simp only [if_neg boundary,if_neg wordNonboundary]
          exact ih (index+1) (sourceCallerSquare value) (by omega)

theorem original_full_uint32_search_is_the_actual_original_word_search
    (m : Nat) (value : CanonicalScalar) (positive : 1≤m) (bounded : m≤32) :
    sourceUInt32SearchWalk (UInt32.ofNat m) m 0 value =
      TransferBlstArmSqrtSearch01.sourceWordSearch m value := by
  exact complete_original_uint32_search_counter_is_the_qualified_original_word_search m m 0 value (by omega) bounded

def sourceUInt32CorrectionCount (m index : Nat) : Nat :=
  ((UInt32.ofNat m)-(UInt32.ofNat index)-1).toNat

theorem successful_original_word_search_derives_the_exact_unsigned_correction_count
    (m index : Nat) (value : CanonicalScalar) (bounded : m≤32)
    (success : TransferBlstArmSqrtSearch01.sourceWordSearch m value = some index) :
    sourceUInt32CorrectionCount m index = m-index-1 := by
  have below := TransferCommonwareSqrtSchedule01.every_successful_source_search_returns_an_index_below_m
    m index (TransferBlstArmNormalized01.sourceBlstFrWordMeaning value.words)
    ((TransferBlstArmSqrtSearch01.actual_original_word_inner_search_is_the_qualified_source_search m value).symm.trans success)
  rw [sourceUInt32CorrectionCount,← UInt32.ofNat_sub (Nat.le_of_lt below)]
  change ((UInt32.ofNat (m-index))-(UInt32.ofNat 1)).toNat = _
  rw [← UInt32.ofNat_sub (by omega : 1≤m-index)]
  have fits : m-index-1 < UInt32.size := by change m-index-1 < 4294967296; omega
  rw [UInt32.toNat_ofNat_of_lt' fits]

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceUInt32SearchWalk
#print axioms sourceUInt32SearchWalk
set_option pp.all true in
#check @original_small_index_word_encoding_is_injective
#print axioms original_small_index_word_encoding_is_injective
set_option pp.all true in
#check @complete_original_uint32_search_counter_is_the_qualified_original_word_search
#print axioms complete_original_uint32_search_counter_is_the_qualified_original_word_search
set_option pp.all true in
#check @original_full_uint32_search_is_the_actual_original_word_search
#print axioms original_full_uint32_search_is_the_actual_original_word_search
set_option pp.all true in
#check @sourceUInt32CorrectionCount
#print axioms sourceUInt32CorrectionCount
set_option pp.all true in
#check @successful_original_word_search_derives_the_exact_unsigned_correction_count
#print axioms successful_original_word_search_derives_the_exact_unsigned_correction_count
end ShielddSecurity.TransferBlstArmSqrtIndices01
