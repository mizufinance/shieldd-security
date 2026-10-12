import ShielddSecurity.TransferCheckedWordWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordBlockDriver01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
attribute [local irreducible] TransferScalarCanonicalKey01.canonicalScalarForKey
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferNullifierBatchSource01 (Backend BatchError)
open TransferCheckedWordStageRefinement01 (previousPending)
open TransferCheckedWordSeal01 (sealFields sealAtKey)
open TransferCheckedWordWalk01 (walk)
open TransferWordSctPendingRead01 (sourceOrdered sourceIsSealed sourceEnsureSealed)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Constructed public checked-word whole-block walk followed by checked
source seal derives its actual final getter of the exact original global
canonical source fields, uniqueness/capacity, durable false observations and
other-key frames. Only observed initial selected absence and returned run
success are supplied. No caller intermediate walk, desired value, getter,
codec inverse, supported type-domain or invariant is assumed. Native full
source selector/Any/Clone/imbl/Scalar/reader/compiler/trace binding remains OPEN. -/

def allFields (batches : List (List CanonicalScalar × Bool)) : List CanonicalScalar :=
  batches.flatMap Prod.fst

def run {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (parent : View (WordTaggedObject Other)) (writes : Writes (WordTaggedObject Other))
    (key : Nat) (batches : List (List CanonicalScalar × Bool)) :
    Except Unit (Except BatchError (Writes (WordTaggedObject Other))) :=
  (walk backend child parent key writes batches).bind fun result =>
    match result with
    | .error refusal => .ok (.error refusal)
    | .ok staged => (sealAtKey parent staged key).map (fun result => result.mapError (fun _ => BatchError.sealed))

theorem returned_run_derives_actual_walk_then_checked_seal {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes final : Writes (WordTaggedObject Other)) (key : Nat) (batches : List (List CanonicalScalar × Bool))
    (returned : run backend child parent writes key batches = .ok (.ok final)) :
    ∃ staged, walk backend child parent key writes batches = .ok (.ok staged) ∧
      sealAtKey parent staged key = .ok (.ok final) := by
  unfold run at returned
  cases walking : walk backend child parent key writes batches with
  | error panic => rw [walking] at returned; cases returned
  | ok result =>
    rw [walking] at returned
    cases result with
    | error refusal => cases returned
    | ok staged =>
      cases sealing : sealAtKey parent staged key with
      | error panic => rw [sealing] at returned; cases returned
      | ok result =>
        rw [sealing] at returned
        cases result with
        | error refusal => cases returned
        | ok sealedWrites =>
          have same : sealedWrites = final := Except.ok.inj (Except.ok.inj returned)
          subst final
          exact ⟨staged, rfl, rfl⟩

theorem returned_checked_cache_seal_preserves_actual_projected_order_and_other_keys {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes final : Writes (WordTaggedObject Other)) (key : Nat)
    (returned : sealAtKey parent writes key = .ok (.ok final)) :
    ∃ fields : List CanonicalScalar,
      (overlay parent final) key = some (.inl (.sealed fields)) ∧
      fields.map (fun scalar => scalarKey scalar.words) = (previousPending ((overlay parent writes) key)).ordered ∧
      ∀ other, other ≠ key → final other = writes other := by
  unfold sealAtKey at returned
  simp only [Except.map] at returned
  cases sealedResult : sealFields ((overlay parent writes) key) with
  | error panic => rw [sealedResult] at returned; cases returned
  | ok result =>
    rw [sealedResult] at returned
    cases result with
    | error refusal => cases returned
    | ok object =>
      obtain ⟨fields, prior, same⟩ :=
        TransferCheckedWordSeal01.returned_seal_derives_actual_prior_absent_or_open_and_exact_original_fields
          ((overlay parent writes) key) object sealedResult
      have cached := (Except.ok.inj (Except.ok.inj returned)).symm
      rw [same] at cached
      have atKey : final key = some (some (.inl (.sealed fields))) := by
        rw [cached]
        exact if_pos rfl
      refine ⟨fields, ?_, ?_, ?_⟩
      · simp only [overlay, atKey]
      · cases prior with
        | inl absent =>
          obtain ⟨absent, empty⟩ := absent
          rw [absent, empty]
          rfl
        | inr opened =>
          obtain ⟨members, selected⟩ := opened
          rw [selected]
          rfl
      · intro other different
        rw [cached]
        exact if_neg different

theorem returned_whole_checked_block_derives_actual_exact_original_global_field_getter {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes final : Writes (WordTaggedObject Other)) (key : Nat) (batches : List (List CanonicalScalar × Bool))
    (initiallyAbsent : (overlay parent writes) key = none)
    (returned : run backend child parent writes key batches = .ok (.ok final)) :
    (overlay parent final) key = some (.inl (.sealed (allFields batches))) ∧
      sourceOrdered ((overlay parent final) key) = .ok (allFields batches) ∧
      sourceIsSealed ((overlay parent final) key) = .ok true ∧
      sourceEnsureSealed ((overlay parent final) key) = .ok (.ok ()) ∧
      (allFields batches).length ≤ blockCapacity ∧
      ((allFields batches).map (fun scalar => scalarKey scalar.words)).Nodup ∧
      (∀ nullifier ∈ (allFields batches).map (fun scalar => scalarKey scalar.words), backend.lookup child nullifier = some false) ∧
      (∀ other, other ≠ key → final other = writes other ∧ (overlay parent final) other = (overlay parent writes) other) := by
  obtain ⟨staged, walked, sealedReturned⟩ := returned_run_derives_actual_walk_then_checked_seal
    backend child parent writes final key batches returned
  have initialInvariant : TransferPendingSetInvariant01.Invariant blockCapacity (previousPending ((overlay parent writes) key)) := by
    rw [initiallyAbsent]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  obtain ⟨invariant, ordered, unspent, walkFrames⟩ :=
    TransferCheckedWordWalk01.returned_whole_walk_derives_global_order_invariant_unspent_and_frames
      backend child parent key batches writes staged initialInvariant walked
  have globalKeys : batches.flatMap (fun batch => batch.1.map (fun scalar => scalarKey scalar.words)) =
      (allFields batches).map (fun scalar => scalarKey scalar.words) := by
    exact (List.map_flatMap (l := batches)).symm
  rw [initiallyAbsent] at ordered
  change (previousPending ((overlay parent staged) key)).ordered = [] ++ _ at ordered
  rw [List.nil_append, globalKeys] at ordered
  rw [globalKeys] at unspent
  obtain ⟨fields, actual, preserved, sealFrames⟩ :=
    returned_checked_cache_seal_preserves_actual_projected_order_and_other_keys parent staged final key sealedReturned
  have equalKeys : fields.map (fun scalar => scalarKey scalar.words) =
      (allFields batches).map (fun scalar => scalarKey scalar.words) := preserved.trans ordered
  have exactFields : fields = allFields batches :=
    (TransferCanonicalSourceWordRetention01.canonical_source_scalar_list_recovers_exact_ordered_original_fields fields).symm.trans
      ((congrArg (fun keys => keys.map TransferCanonicalWordPending01.encodeWordScalar) equalKeys).trans
        (TransferCanonicalSourceWordRetention01.canonical_source_scalar_list_recovers_exact_ordered_original_fields (allFields batches)))
  rw [exactFields] at actual
  have capacity : (allFields batches).length ≤ blockCapacity := by
    have bounded := invariant.2.2.1
    rw [ordered, List.length_map] at bounded
    exact bounded
  have unique : ((allFields batches).map (fun scalar => scalarKey scalar.words)).Nodup := by
    rw [← ordered]
    exact invariant.2.1
  refine ⟨actual, ?_, ?_, ?_, capacity, unique, unspent, ?_⟩
  · rw [actual]; rfl
  · rw [actual]; rfl
  · rw [actual]; rfl
  · intro other different
    have framed := (sealFrames other different).trans (walkFrames other different).1
    refine ⟨framed, ?_⟩
    simp only [overlay, framed]

set_option pp.all true in
#check @allFields
#print axioms allFields
set_option pp.all true in
#check @run
#print axioms run
set_option pp.all true in
#check @returned_run_derives_actual_walk_then_checked_seal
#print axioms returned_run_derives_actual_walk_then_checked_seal
set_option pp.all true in
#check @returned_checked_cache_seal_preserves_actual_projected_order_and_other_keys
#print axioms returned_checked_cache_seal_preserves_actual_projected_order_and_other_keys
set_option pp.all true in
#check @returned_whole_checked_block_derives_actual_exact_original_global_field_getter
#print axioms returned_whole_checked_block_derives_actual_exact_original_global_field_getter
end ShielddSecurity.TransferCheckedWordBlockDriver01
