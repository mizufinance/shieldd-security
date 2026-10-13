import ShielddSecurity.TransferBlstArmNormalized01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCaller01
open TransferBlstArmNormalized01
open TransferBlstByteCaller01
open TransferBlstEncoder01 (sourceBEFromLimbs64)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] Vector.ofFn sourceArmFromMontVector sourceScalarLEBytes64 sourceLEParseMemory64 sourceBEFromLimbs64

/-- Three separate typed allocations used by the Rust caller. This models
source writes and frames; pointer separation, ABI and compiler execution must
still be established for the actual native call. -/
abbrev CallerMemory := Vector UInt64 4 × Vector UInt8 32 × Vector UInt8 32

/-- The caller's nonalias scalar_from_fr branch, including the LE write. -/
def sourceScalarFromFr (memory : CallerMemory) : CallerMemory :=
  (memory.1,sourceScalarLEBytes64 (sourceArmFromMontVector memory.1),memory.2.2)

/-- The bendian_from_scalar parser and writer, with arbitrary parser scratch. -/
def sourceBendianFromScalar (memory : CallerMemory) (scratch : Vector UInt64 4) : CallerMemory :=
  (memory.1,memory.2.1,Vector.ofFn (sourceBEFromLimbs64 (sourceLEParseMemory64 memory.2.1 scratch)))

def sourceAsSlice (memory : CallerMemory) (scratch : Vector UInt64 4) : CallerMemory :=
  sourceBendianFromScalar (sourceScalarFromFr memory) scratch

theorem scalar_from_fr_preserves_input_and_output_allocations (memory : CallerMemory) :
    (sourceScalarFromFr memory).1 = memory.1 ∧
      (sourceScalarFromFr memory).2.2 = memory.2.2 := by
  exact ⟨rfl,rfl⟩

theorem bendian_from_scalar_preserves_input_and_scalar_allocations
    (memory : CallerMemory) (scratch : Vector UInt64 4) :
    (sourceBendianFromScalar memory scratch).1 = memory.1 ∧
      (sourceBendianFromScalar memory scratch).2.1 = memory.2.1 := by
  exact ⟨rfl,rfl⟩

theorem caller_as_slice_derives_every_original_input_field_byte
    (memory : CallerMemory) (scratch : Vector UInt64 4) (index : Fin 32) :
    (sourceAsSlice memory scratch).2.2[index.val] =
      TransferCommonwareMapBytes01.canonicalBEByte (sourceBlstFrWordMeaning memory.1) index := by
  simp only [sourceAsSlice,sourceBendianFromScalar,sourceScalarFromFr,Vector.getElem_ofFn]
  have parsed := TransferBlstByteRoundtrip01.actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector
    (sourceArmFromMontVector memory.1) scratch
  have written := congrArg (fun words : Vector UInt64 4 => sourceBEFromLimbs64 words index) parsed
  exact written.trans (TransferBlstFullBytes01.actual_be_encoder_every_byte_derives_canonical_field_byte_from_normalized_value
    (sourceArmFromMontVector memory.1) (sourceBlstFrWordMeaning memory.1)
    (actual_full_from_mont_output_derives_its_input_representation_field_value memory.1) index)

theorem caller_as_slice_preserves_original_input_words
    (memory : CallerMemory) (scratch : Vector UInt64 4) :
    (sourceAsSlice memory scratch).1 = memory.1 := rfl

theorem caller_as_slice_is_independent_of_prior_byte_allocations_and_parser_scratch
    (words : Vector UInt64 4) (scalarA scalarB outputA outputB : Vector UInt8 32)
    (scratchA scratchB : Vector UInt64 4) :
    (sourceAsSlice (words,scalarA,outputA) scratchA).2.2 =
      (sourceAsSlice (words,scalarB,outputB) scratchB).2.2 := by
  apply Vector.ext
  intro index inside
  rw [caller_as_slice_derives_every_original_input_field_byte _ _ ⟨index,inside⟩,
    caller_as_slice_derives_every_original_input_field_byte _ _ ⟨index,inside⟩]

def sourceCallerSignGuard (choice : Bool) (memory : CallerMemory) (scratch : Vector UInt64 4) : Bool :=
  (((sourceAsSlice memory scratch).2.2[31] &&& 1).toNat == 1) != choice

theorem caller_byte31_mask_derives_original_input_field_parity
    (memory : CallerMemory) (scratch : Vector UInt64 4) :
    ((sourceAsSlice memory scratch).2.2[31] &&& 1).toNat = (sourceBlstFrWordMeaning memory.1).val % 2 := by
  rw [caller_as_slice_derives_every_original_input_field_byte _ _ ⟨31,by decide⟩]
  exact TransferCommonwareMapBytes01.canonical_commonware_be_byte31_mask_derives_the_field_parity _

theorem caller_sign_guard_derives_the_original_input_field_guard
    (choice : Bool) (memory : CallerMemory) (scratch : Vector UInt64 4) :
    sourceCallerSignGuard choice memory scratch =
      (((sourceBlstFrWordMeaning memory.1).val % 2 == 1) != choice) := by
  rw [sourceCallerSignGuard,caller_byte31_mask_derives_original_input_field_parity]

/-- The selected field meaning follows the source guard. The native cneg
implementation's representation correspondence remains a separate obligation. -/
def sourceCallerSelectedMeaning (choice : Bool) (memory : CallerMemory) (scratch : Vector UInt64 4) :
    ZMod nullifierModulus :=
  if sourceCallerSignGuard choice memory scratch then -sourceBlstFrWordMeaning memory.1
    else sourceBlstFrWordMeaning memory.1

theorem caller_selected_meaning_derives_the_qualified_root_normalizer
    (choice : Bool) (memory : CallerMemory) (scratch : Vector UInt64 4) :
    sourceCallerSelectedMeaning choice memory scratch =
      TransferCommonwareMapRoots01.normalizeRoot choice (sourceBlstFrWordMeaning memory.1) := by
  rw [sourceCallerSelectedMeaning,caller_sign_guard_derives_the_original_input_field_guard]
  cases choice with
  | false =>
    by_cases low : (sourceBlstFrWordMeaning memory.1).val % 2 = 0
    · simp [TransferCommonwareMapRoots01.normalizeRoot,low]
    · have one : (sourceBlstFrWordMeaning memory.1).val % 2 = 1 := by omega
      simp [TransferCommonwareMapRoots01.normalizeRoot,one]
  | true =>
    by_cases one : (sourceBlstFrWordMeaning memory.1).val % 2 = 1 <;>
      simp [TransferCommonwareMapRoots01.normalizeRoot,one]
set_option pp.all true in
#check @CallerMemory
#print axioms CallerMemory
set_option pp.all true in
#check @sourceScalarFromFr
#print axioms sourceScalarFromFr
set_option pp.all true in
#check @sourceBendianFromScalar
#print axioms sourceBendianFromScalar
set_option pp.all true in
#check @sourceAsSlice
#print axioms sourceAsSlice
set_option pp.all true in
#check @scalar_from_fr_preserves_input_and_output_allocations
#print axioms scalar_from_fr_preserves_input_and_output_allocations
set_option pp.all true in
#check @bendian_from_scalar_preserves_input_and_scalar_allocations
#print axioms bendian_from_scalar_preserves_input_and_scalar_allocations
set_option pp.all true in
#check @caller_as_slice_derives_every_original_input_field_byte
#print axioms caller_as_slice_derives_every_original_input_field_byte
set_option pp.all true in
#check @caller_as_slice_preserves_original_input_words
#print axioms caller_as_slice_preserves_original_input_words
set_option pp.all true in
#check @caller_as_slice_is_independent_of_prior_byte_allocations_and_parser_scratch
#print axioms caller_as_slice_is_independent_of_prior_byte_allocations_and_parser_scratch
set_option pp.all true in
#check @sourceCallerSignGuard
#print axioms sourceCallerSignGuard
set_option pp.all true in
#check @caller_byte31_mask_derives_original_input_field_parity
#print axioms caller_byte31_mask_derives_original_input_field_parity
set_option pp.all true in
#check @caller_sign_guard_derives_the_original_input_field_guard
#print axioms caller_sign_guard_derives_the_original_input_field_guard
set_option pp.all true in
#check @sourceCallerSelectedMeaning
#print axioms sourceCallerSelectedMeaning
set_option pp.all true in
#check @caller_selected_meaning_derives_the_qualified_root_normalizer
#print axioms caller_selected_meaning_derives_the_qualified_root_normalizer
end ShielddSecurity.TransferBlstArmCaller01
