import ShielddSecurity.TransferBlstArmPending01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmNullifierReader01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferBlstArmStage01 (sourceOriginalOrdContains)
open TransferNullifierBatchSource01 (BatchError)
attribute [local irreducible] scalarKey

/-! The SCT Nullifier is SDK jubjub::Fq, not a Commonware blst Scalar.
Its Ord reverses SDK little-endian serialization; its Eq compares the original
four words. The previously checked serialization/comparator bridge identifies
these observations on the explicit canonical word domain. Reader lookup owns
the authenticated durable-key contract. Concrete Rust collections, private
value producers, Any/Clone, async and compiler execution remain separate. -/

def sourcePendingContains (pending : WordNativePending) (field : CanonicalScalar) : Bool :=
  match pending with
  | .opened _ members => TransferCanonicalSourceMembership01.sourceOrdContains members field
  | .sealed ordered => ordered.any (fun candidate => decide (candidate.words = field.words))

def sourcePendingKeys (pending : WordNativePending) : List Nat :=
  match pending with
  | .opened _ members => members.map (fun field => scalarKey field.words)
  | .sealed ordered => ordered.map (fun field => scalarKey field.words)

theorem original_sdk_word_equality_is_exact_canonical_source_key_equality
    (left right : CanonicalScalar) : left.words = right.words ↔ scalarKey left.words = scalarKey right.words := by
  constructor
  · intro same
    exact congrArg scalarKey same
  · intro same
    exact congrArg CanonicalScalar.words
      (TransferCanonicalSourceMembership01.canonical_source_key_is_injective_on_entire_typed_fields same)

theorem original_open_or_sealed_pending_contains_is_exact_original_key_membership
    (pending : WordNativePending) (field : CanonicalScalar) :
    sourcePendingContains pending field = (sourcePendingKeys pending).contains (scalarKey field.words) := by
  cases pending with
  | opened ordered members =>
      exact TransferCanonicalSourceMembership01.source_ord_membership_is_exact_mapped_key_membership members field
  | sealed ordered =>
      apply Bool.eq_iff_iff.mpr
      change ordered.any (fun candidate => decide (candidate.words = field.words)) = true ↔
        (ordered.map (fun candidate => scalarKey candidate.words)).contains (scalarKey field.words) = true
      rw [List.any_eq_true, List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨candidate, inside, same⟩
        exact ⟨candidate, inside, (original_sdk_word_equality_is_exact_canonical_source_key_equality candidate field).mp (of_decide_eq_true same)⟩
      · rintro ⟨candidate, inside, same⟩
        exact ⟨candidate, inside, decide_eq_true ((original_sdk_word_equality_is_exact_canonical_source_key_equality candidate field).mpr same)⟩

def sourceLookupFields (lookup : Nat → Option Bool) : List CanonicalScalar → Option (List Bool)
  | [] => some []
  | field :: rest => (lookup (scalarKey field.words)).bind fun flag =>
      (sourceLookupFields lookup rest).map fun flags => flag :: flags

theorem actual_typed_reader_map_is_exact_original_key_lookup_walk
    (lookup : Nat → Option Bool) (fields : List CanonicalScalar) :
    sourceLookupFields lookup fields = TransferNullifierReaderVector01.lookupAll lookup
      (fields.map (fun field => scalarKey field.words)) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      simp only [sourceLookupFields, List.map_cons, TransferNullifierReaderVector01.lookupAll, ih]

def sourceJoinFields (pending : WordNativePending) : List CanonicalScalar → List Bool → List Bool
  | [], flags => flags
  | _, [] => []
  | field :: rest, flag :: flags =>
      (flag || sourcePendingContains pending field) :: sourceJoinFields pending rest flags

theorem actual_typed_in_place_zip_is_exact_original_key_pending_join
    (pending : WordNativePending) (fields : List CanonicalScalar) (flags : List Bool) :
    sourceJoinFields pending fields flags = TransferNullifierReaderVector01.joinPending
      (fun key => (sourcePendingKeys pending).contains key)
      (fields.map (fun field => scalarKey field.words)) flags := by
  induction fields generalizing flags with
  | nil => rfl
  | cons field rest ih =>
      cases flags with
      | nil => rfl
      | cons flag flags =>
          simp only [sourceJoinFields, List.map_cons, TransferNullifierReaderVector01.joinPending,
            original_open_or_sealed_pending_contains_is_exact_original_key_membership, ih]

def sourceContainsFields (available : Bool) (lookup : Nat → Option Bool)
    (pending : WordNativePending) (fields : List CanonicalScalar) : Option (List Bool) :=
  if available then (sourceLookupFields lookup fields).map (sourceJoinFields pending fields) else none

theorem actual_typed_contains_is_exact_original_key_reader_and_pending_join
    (available : Bool) (lookup : Nat → Option Bool) (pending : WordNativePending)
    (fields : List CanonicalScalar) :
    sourceContainsFields available lookup pending fields = TransferNullifierReaderVector01.contains
      available lookup (fun key => (sourcePendingKeys pending).contains key)
      (fields.map (fun field => scalarKey field.words)) := by
  have joined : sourceJoinFields pending fields = TransferNullifierReaderVector01.joinPending
      (fun key => (sourcePendingKeys pending).contains key)
      (fields.map (fun field => scalarKey field.words)) := by
    funext flags
    exact actual_typed_in_place_zip_is_exact_original_key_pending_join pending fields flags
  simp only [sourceContainsFields, TransferNullifierReaderVector01.contains,
    actual_typed_reader_map_is_exact_original_key_lookup_walk,joined]

def sourceReaderCheck (available : Bool) (lookup : Nat → Option Bool)
    (pending : WordNativePending) (fields : List CanonicalScalar) : Except BatchError Unit :=
  match sourceContainsFields available lookup pending fields with
  | none => .error .reader
  | some flags =>
      if TransferNullifierReaderVector01.zipUnspent
          (fields.map (fun field => scalarKey field.words)) flags then .ok () else .error .spent

theorem returned_original_reader_check_derives_full_vector_and_every_original_input_unspent
    (available : Bool) (lookup : Nat → Option Bool) (pending : WordNativePending)
    (fields : List CanonicalScalar) (returned : sourceReaderCheck available lookup pending fields = .ok ()) :
    available = true ∧ ∃ flags,
      sourceContainsFields available lookup pending fields = some flags ∧ flags.length = fields.length ∧
      ∀ field ∈ fields, lookup (scalarKey field.words) = some false ∧ sourcePendingContains pending field = false := by
  cases observed : sourceContainsFields available lookup pending fields with
  | none => simp only [sourceReaderCheck, observed] at returned; cases returned
  | some flags =>
      have unspent : TransferNullifierReaderVector01.zipUnspent
          (fields.map (fun field => scalarKey field.words)) flags = true := by
        simp only [sourceReaderCheck, observed] at returned
        split at returned
        · assumption
        · cases returned
      have actual := observed
      rw [actual_typed_contains_is_exact_original_key_reader_and_pending_join] at actual
      obtain ⟨gate, _, _, _, _, _⟩ := TransferNullifierReaderVector01.contains_success_actual_vector
        available lookup (fun key => (sourcePendingKeys pending).contains key) _ flags actual
      obtain ⟨width, each⟩ := TransferNullifierReaderVector01.contains_success_unspent
        available lookup (fun key => (sourcePendingKeys pending).contains key) _ flags actual unspent
      refine ⟨gate, flags, rfl, ?_, ?_⟩
      · simpa only [List.length_map] using width
      · intro field inside
        have keyInside : scalarKey field.words ∈ fields.map (fun field => scalarKey field.words) :=
          List.mem_map.mpr ⟨field, inside, rfl⟩
        have checked := each (scalarKey field.words) keyInside
        exact ⟨checked.1, (original_open_or_sealed_pending_contains_is_exact_original_key_membership pending field).trans checked.2⟩
set_option pp.all true in
#check @sourcePendingContains
#print axioms sourcePendingContains
set_option pp.all true in
#check @sourcePendingKeys
#print axioms sourcePendingKeys
set_option pp.all true in
#check @original_sdk_word_equality_is_exact_canonical_source_key_equality
#print axioms original_sdk_word_equality_is_exact_canonical_source_key_equality
set_option pp.all true in
#check @original_open_or_sealed_pending_contains_is_exact_original_key_membership
#print axioms original_open_or_sealed_pending_contains_is_exact_original_key_membership
set_option pp.all true in
#check @sourceLookupFields
#print axioms sourceLookupFields
set_option pp.all true in
#check @actual_typed_reader_map_is_exact_original_key_lookup_walk
#print axioms actual_typed_reader_map_is_exact_original_key_lookup_walk
set_option pp.all true in
#check @sourceJoinFields
#print axioms sourceJoinFields
set_option pp.all true in
#check @actual_typed_in_place_zip_is_exact_original_key_pending_join
#print axioms actual_typed_in_place_zip_is_exact_original_key_pending_join
set_option pp.all true in
#check @sourceContainsFields
#print axioms sourceContainsFields
set_option pp.all true in
#check @actual_typed_contains_is_exact_original_key_reader_and_pending_join
#print axioms actual_typed_contains_is_exact_original_key_reader_and_pending_join
set_option pp.all true in
#check @sourceReaderCheck
#print axioms sourceReaderCheck
set_option pp.all true in
#check @returned_original_reader_check_derives_full_vector_and_every_original_input_unspent
#print axioms returned_original_reader_check_derives_full_vector_and_every_original_input_unspent
end ShielddSecurity.TransferBlstArmNullifierReader01
