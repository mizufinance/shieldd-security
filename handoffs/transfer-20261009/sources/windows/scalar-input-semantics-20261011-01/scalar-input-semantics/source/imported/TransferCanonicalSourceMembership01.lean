import ShielddSecurity.TransferCanonicalSourcePublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalSourceMembership01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
attribute [local irreducible] TransferScalarCanonicalKey01.canonicalScalarForKey
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (encodeWordScalar)
open TransferScalarLittleEndianBytes01 (scalarKey serializerBytes)
open TransferScalarReversedByteOrder01 (compareHighFirst)
open TransferCanonicalSourcePublication01 (canonicalSourceFields)
open TransferStateDelta
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferBoundedNativeCodec01 (ExtendedObject)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
open TransferWordSourceDriver01 (runCompleteBlock)
/-! Canonical source fields, their numeric source keys and modeled source Ord
equality describe the same finite membership and duplicate observations.
Successful whole publication derives original field uniqueness and capacity.
Actual Rust Ord/PartialEq/iterators/BTreeSet/imbl/private Scalar invariant and
compiler/ownership semantics remain separate. Source model observations only;
no native/control/certification or ancestor replay credit. -/

theorem canonical_source_key_is_injective_on_entire_typed_fields :
    Function.Injective (fun scalar : CanonicalScalar => scalarKey scalar.words) := by
  intro left right same
  exact (TransferCanonicalSourceWordRetention01.source_key_word_encoder_recovers_entire_canonical_typed_scalar left).symm.trans
    ((congrArg encodeWordScalar same).trans
      (TransferCanonicalSourceWordRetention01.source_key_word_encoder_recovers_entire_canonical_typed_scalar right))

def sourceOrdContains (fields : List CanonicalScalar) (scalar : CanonicalScalar) : Bool :=
  fields.any (fun candidate => decide
    (compareHighFirst (serializerBytes candidate.words.toList).reverse (serializerBytes scalar.words.toList).reverse = .eq))

theorem source_ord_equality_is_exact_source_key_equality (left right : CanonicalScalar) :
    compareHighFirst (serializerBytes left.words.toList).reverse (serializerBytes right.words.toList).reverse = .eq ↔
      scalarKey left.words = scalarKey right.words := by
  rw [TransferScalarReversedByteOrder01.source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order,
    Nat.compare_eq_eq, TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]

theorem source_ord_membership_is_exact_mapped_key_membership (fields : List CanonicalScalar) (scalar : CanonicalScalar) :
    sourceOrdContains fields scalar = (fields.map (fun field => scalarKey field.words)).contains (scalarKey scalar.words) := by
  apply Bool.eq_iff_iff.mpr
  change sourceOrdContains fields scalar = true ↔ (fields.map (fun field => scalarKey field.words)).contains (scalarKey scalar.words) = true
  rw [sourceOrdContains, List.any_eq_true, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨candidate, inside, comparison⟩
    exact ⟨candidate, inside, (source_ord_equality_is_exact_source_key_equality candidate scalar).mp (of_decide_eq_true comparison)⟩
  · rintro ⟨candidate, inside, sameKey⟩
    exact ⟨candidate, inside, decide_eq_true ((source_ord_equality_is_exact_source_key_equality candidate scalar).mpr sameKey)⟩

theorem mapped_source_key_uniqueness_iff_original_typed_field_uniqueness (fields : List CanonicalScalar) :
    (fields.map (fun field => scalarKey field.words)).Nodup ↔ fields.Nodup := by
  constructor
  · intro projected
    exact List.Pairwise.of_map (fun field : CanonicalScalar => scalarKey field.words)
      (fun _ _ different same => different (congrArg (fun field : CanonicalScalar => scalarKey field.words) same)) projected
  · intro original
    exact List.Pairwise.map (fun field : CanonicalScalar => scalarKey field.words)
      (fun _ _ different same => different (canonical_source_key_is_injective_on_entire_typed_fields same)) original

theorem returned_whole_canonical_source_publication_derives_original_field_uniqueness_capacity_and_membership {Other E K X Tree A I : Type}
    (inputs : A → List I) (scalarOf : I → CanonicalScalar)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs (fun input => (scalarOf input).words) sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    (canonicalSourceFields inputs scalarOf sourceRequests).Nodup ∧
      (canonicalSourceFields inputs scalarOf sourceRequests).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      ∀ scalar, sourceOrdContains (canonicalSourceFields inputs scalarOf sourceRequests) scalar =
        ((canonicalSourceFields inputs scalarOf sourceRequests).map (fun field => scalarKey field.words)).contains (scalarKey scalar.words) := by
  obtain ⟨_, _, _, _, _, keys, _, _, _, unique, capacity, _, _, _, _, _, _, _⟩ :=
    TransferCanonicalSourcePublication01.returned_whole_canonical_source_driver_publishes_original_fields_checked_getter_and_exact_boundary
      inputs scalarOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height outcome root returned success
  rw [keys] at unique capacity
  rw [List.length_map] at capacity
  exact ⟨(mapped_source_key_uniqueness_iff_original_typed_field_uniqueness _).mp unique, capacity,
    fun scalar => source_ord_membership_is_exact_mapped_key_membership _ scalar⟩

set_option pp.all true in
#check @canonical_source_key_is_injective_on_entire_typed_fields
#print axioms canonical_source_key_is_injective_on_entire_typed_fields
set_option pp.all true in
#check @sourceOrdContains
#print axioms sourceOrdContains
set_option pp.all true in
#check @source_ord_equality_is_exact_source_key_equality
#print axioms source_ord_equality_is_exact_source_key_equality
set_option pp.all true in
#check @source_ord_membership_is_exact_mapped_key_membership
#print axioms source_ord_membership_is_exact_mapped_key_membership
set_option pp.all true in
#check @mapped_source_key_uniqueness_iff_original_typed_field_uniqueness
#print axioms mapped_source_key_uniqueness_iff_original_typed_field_uniqueness
set_option pp.all true in
#check @returned_whole_canonical_source_publication_derives_original_field_uniqueness_capacity_and_membership
#print axioms returned_whole_canonical_source_publication_derives_original_field_uniqueness_capacity_and_membership
end ShielddSecurity.TransferCanonicalSourceMembership01
