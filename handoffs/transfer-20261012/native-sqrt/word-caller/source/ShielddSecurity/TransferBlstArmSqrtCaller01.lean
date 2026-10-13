import ShielddSecurity.TransferBlstArmSqrtWhile01
import ShielddSecurity.TransferBlstArmCneg01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtCaller01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmSqrtWhile01 (sourceWordSqrt)
open TransferBlstArmCneg01 (sourceCallerCorrectedRoot)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceWordSqrt sourceCallerCorrectedRoot sourceBlstFrWordMeaning

/-! A returned original word-source sqrt feeds the actual caller byte guard
and ARM conditional-negation transcription. Its square, normalized SDK root
and every resulting caller byte are derived. Inverse completeness and actual
native execution remain open; no total native sqrt contract is inferred. -/

def sourceNormalizedWordSqrt (input : CanonicalScalar) (actualInverse scratch : Vector UInt64 4)
    (choice : Bool) : Option CanonicalScalar :=
  (sourceWordSqrt input actualInverse).map (fun root => sourceCallerCorrectedRoot choice root scratch)

theorem returned_original_word_sqrt_derives_an_original_sdk_root
    (input root : CanonicalScalar) (actualInverse : Vector UInt64 4)
    (success : sourceWordSqrt input actualInverse = some root) :
    ∃ sdkRoot, TransferFfFieldApi01.sourceSdkFieldSqrt (sourceBlstFrWordMeaning input.words) = some sdkRoot ∧
      sdkRoot * sdkRoot = sourceBlstFrWordMeaning root.words * sourceBlstFrWordMeaning root.words := by
  have checked := TransferBlstArmSqrtWhile01.returned_complete_original_word_source_sqrt_derives_original_input_square_without_inverse_correctness
    input root actualInverse success
  obtain ⟨sdkRoot,sdkSuccess⟩ := TransferFfFieldApi01.actual_source_sdk_field_sqrt_is_complete
    (sourceBlstFrWordMeaning input.words) ⟨sourceBlstFrWordMeaning root.words,by simpa only [pow_two] using checked.symm⟩
  exact ⟨sdkRoot,sdkSuccess,(TransferFfFieldApi01.actual_source_sdk_field_sqrt_is_sound _ _ sdkSuccess).trans
    (by simpa only [pow_two] using checked.symm)⟩

theorem original_word_sqrt_byte_guard_and_cneg_derive_the_normalized_sdk_root
    (input root : CanonicalScalar) (actualInverse scratch : Vector UInt64 4) (choice : Bool)
    (success : sourceWordSqrt input actualInverse = some root) :
    ∃ sdkRoot, TransferFfFieldApi01.sourceSdkFieldSqrt (sourceBlstFrWordMeaning input.words) = some sdkRoot ∧
      sourceBlstFrWordMeaning (sourceCallerCorrectedRoot choice root scratch).words =
        TransferCommonwareMapRoots01.normalizeRoot choice sdkRoot := by
  obtain ⟨sdkRoot,sdkSuccess,squares⟩ := returned_original_word_sqrt_derives_an_original_sdk_root input root actualInverse success
  refine ⟨sdkRoot,sdkSuccess,?_⟩
  rw [TransferBlstArmCneg01.original_caller_byte_guard_and_cneg_derive_the_same_canonical_root]
  exact TransferCommonwareMapRoots01.equal_squares_derive_equal_actual_normalized_roots choice _ _ squares.symm

theorem returned_original_normalized_word_sqrt_derives_the_normalized_sdk_root
    (input returned : CanonicalScalar) (actualInverse scratch : Vector UInt64 4) (choice : Bool)
    (success : sourceNormalizedWordSqrt input actualInverse scratch choice = some returned) :
    ∃ sdkRoot, TransferFfFieldApi01.sourceSdkFieldSqrt (sourceBlstFrWordMeaning input.words) = some sdkRoot ∧
      sourceBlstFrWordMeaning returned.words = TransferCommonwareMapRoots01.normalizeRoot choice sdkRoot := by
  unfold sourceNormalizedWordSqrt at success
  cases observed : sourceWordSqrt input actualInverse with
  | none => simp only [observed,Option.map_none] at success; cases success
  | some root =>
      have same : sourceCallerCorrectedRoot choice root scratch = returned := by
        simpa only [observed,Option.map_some,Option.some.injEq] using success
      rw [← same]
      exact original_word_sqrt_byte_guard_and_cneg_derive_the_normalized_sdk_root input root actualInverse scratch choice observed

theorem returned_original_normalized_word_sqrt_derives_every_original_sdk_root_byte
    (input returned : CanonicalScalar) (actualInverse scratch byteScratch : Vector UInt64 4) (choice : Bool)
    (success : sourceNormalizedWordSqrt input actualInverse scratch choice = some returned) :
    ∃ sdkRoot, TransferFfFieldApi01.sourceSdkFieldSqrt (sourceBlstFrWordMeaning input.words) = some sdkRoot ∧
      ∀ index : Fin 32,
        (TransferBlstArmCaller01.sourceAsSlice (returned.words,Vector.replicate 32 0,Vector.replicate 32 0) byteScratch).2.2[index.val] =
          TransferCommonwareMapBytes01.canonicalBEByte (TransferCommonwareMapRoots01.normalizeRoot choice sdkRoot) index := by
  obtain ⟨sdkRoot,sdkSuccess,meaning⟩ := returned_original_normalized_word_sqrt_derives_the_normalized_sdk_root
    input returned actualInverse scratch choice success
  refine ⟨sdkRoot,sdkSuccess,?_⟩
  intro index
  rw [TransferBlstArmCaller01.caller_as_slice_derives_every_original_input_field_byte _ _ index]
  exact congrArg (fun value => TransferCommonwareMapBytes01.canonicalBEByte value index) meaning

set_option pp.all true in
#check @sourceNormalizedWordSqrt
#print axioms sourceNormalizedWordSqrt
set_option pp.all true in
#check @returned_original_word_sqrt_derives_an_original_sdk_root
#print axioms returned_original_word_sqrt_derives_an_original_sdk_root
set_option pp.all true in
#check @original_word_sqrt_byte_guard_and_cneg_derive_the_normalized_sdk_root
#print axioms original_word_sqrt_byte_guard_and_cneg_derive_the_normalized_sdk_root
set_option pp.all true in
#check @returned_original_normalized_word_sqrt_derives_the_normalized_sdk_root
#print axioms returned_original_normalized_word_sqrt_derives_the_normalized_sdk_root
set_option pp.all true in
#check @returned_original_normalized_word_sqrt_derives_every_original_sdk_root_byte
#print axioms returned_original_normalized_word_sqrt_derives_every_original_sdk_root_byte
end ShielddSecurity.TransferBlstArmSqrtCaller01
