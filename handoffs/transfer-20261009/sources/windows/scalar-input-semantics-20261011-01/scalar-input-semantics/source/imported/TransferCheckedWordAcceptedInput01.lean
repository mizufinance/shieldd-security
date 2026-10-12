import ShielddSecurity.TransferCheckedWordFreshSnapshot01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordAcceptedInput01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferNullifierBatchSource01 (Backend)
open TransferCheckedWordBlockDriver01 (allFields)
open TransferCheckedWordFreshSnapshot01 (snapshotObjects runFromSnapshot)
open TransferWordSctPendingRead01 (sourceOrdered)
open TransferScalarLittleEndianBytes01 (scalarKey serializerBytes decodeLE)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Source pending getter then ordered iter/copied/collect writer input is
represented by its exact original fields and mathematical key projection.
Returned fresh whole block determines the actual selected getter input and
complete accepted vector. Global projected keys are canonical, unique and
exact Montgomery values; every original field serializes to32 bytes. Native
Vec/iter/copied/collect/Nullifier Copy/Scalar/reader/writer/ABI/compiler and
complete Host trace binding remains OPEN; no runtime/certification credit. -/

def acceptedKeys {Other : Type} (object : Option (WordTaggedObject Other)) : Except Unit (List Nat) :=
  (sourceOrdered object).map (fun fields => fields.map (fun scalar => scalarKey scalar.words))

theorem symbolic_original_field_key_vector_is_exact_montgomery_value_vector (fields : List CanonicalScalar) :
    fields.map (fun scalar => scalarKey scalar.words) = fields.map (fun scalar => montgomeryValue scalar.words) := by
  have same : (fun scalar : CanonicalScalar => scalarKey scalar.words) =
      (fun scalar : CanonicalScalar => montgomeryValue scalar.words) := funext
    (fun scalar => TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words)
  rw [same]

theorem every_original_typed_field_has_exact_32_byte_canonical_serialized_key (scalar : CanonicalScalar) :
    (serializerBytes scalar.words.toList).length = 32 ∧
      decodeLE (serializerBytes scalar.words.toList) < TransferBoundedNativeCodec01.nullifierModulus ∧
      decodeLE (serializerBytes scalar.words.toList) = montgomeryValue scalar.words := by
  have width := TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width
    scalar.words.toList Vector.length_toList
  have canonical := TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words
  have value := TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words
  unfold scalarKey at canonical value
  exact ⟨width, canonical, value⟩

theorem returned_fresh_whole_block_derives_exact_actual_accepted_key_vector {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (batches : List (List CanonicalScalar × Bool))
    (final : Writes (WordTaggedObject Other)) (returned : runFromSnapshot backend child batches = .ok (.ok final)) :
    acceptedKeys ((overlay snapshotObjects final) (TransferInjectiveKeyPublication01.keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
      .ok ((allFields batches).map (fun scalar => scalarKey scalar.words)) ∧
      acceptedKeys ((overlay snapshotObjects final) (TransferInjectiveKeyPublication01.keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
      .ok ((allFields batches).map (fun scalar => montgomeryValue scalar.words)) ∧
      ((allFields batches).map (fun scalar => scalarKey scalar.words)).Nodup ∧
      (allFields batches).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      (∀ key ∈ (allFields batches).map (fun scalar => scalarKey scalar.words),
        key < TransferBoundedNativeCodec01.nullifierModulus ∧ backend.lookup child key = some false) := by
  obtain ⟨_, getter, _, _, capacity, unique, unspent, _⟩ :=
    TransferCheckedWordFreshSnapshot01.returned_complete_fresh_snapshot_block_derives_exact_actual_global_field_getter
      backend child batches final returned
  have actual : acceptedKeys ((overlay snapshotObjects final)
      (TransferInjectiveKeyPublication01.keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
      .ok ((allFields batches).map (fun scalar => scalarKey scalar.words)) := by
    simp only [acceptedKeys, getter] <;> rfl
  refine ⟨actual, ?_, unique, capacity, ?_⟩
  · rw [actual, symbolic_original_field_key_vector_is_exact_montgomery_value_vector]
  · intro key inside
    obtain ⟨scalar, _, same⟩ := List.mem_map.mp inside
    subst key
    exact ⟨TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words,
      unspent (scalarKey scalar.words) inside⟩

set_option pp.all true in
#check @acceptedKeys
#print axioms acceptedKeys
set_option pp.all true in
#check @symbolic_original_field_key_vector_is_exact_montgomery_value_vector
#print axioms symbolic_original_field_key_vector_is_exact_montgomery_value_vector
set_option pp.all true in
#check @every_original_typed_field_has_exact_32_byte_canonical_serialized_key
#print axioms every_original_typed_field_has_exact_32_byte_canonical_serialized_key
set_option pp.all true in
#check @returned_fresh_whole_block_derives_exact_actual_accepted_key_vector
#print axioms returned_fresh_whole_block_derives_exact_actual_accepted_key_vector
end ShielddSecurity.TransferCheckedWordAcceptedInput01
