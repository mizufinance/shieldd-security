import ShielddSecurity.TransferBlstArmNullifierReader01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmStageReader01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferNullifierBatchSource01 (BatchError)
open TransferBlstArmNullifierReader01 (sourceReaderCheck sourcePendingContains)
open TransferBlstArmPending01 (sourceOriginalStage sourceOriginalUniqueLoop)
open TransferBlstArmStage01 (sourceOriginalOrdContains)
open TransferScalarLittleEndianBytes01 (scalarKey)
attribute [local irreducible] scalarKey

/-! Stage and contains_nullifiers read the same source-model previous object.
The reader uses its actual Open membership/default and authenticated-key
lookup interface. Returned staging success derives required reader availability,
complete flags, every original-field lookup and exact original-field append.
Concrete Any/Clone and mutable-state/async frame preservation, BTreeSet/imbl,
private SDK producers, authenticated lookup and compiler remain native contracts.
Wrong-type fallback in the closure is unreachable after returned whole-stage
success, since the preceding typed object read must have succeeded. -/

def sourceReaderFromPrevious {Other : Type} (previous : Option (WordTaggedObject Other))
    (available : Bool) (lookup : Nat → Option Bool) (fields : List CanonicalScalar) : Except BatchError Unit :=
  match TransferWordObjectRead01.checkedObject previous with
  | .error _ => .error .reader
  | .ok pending => sourceReaderCheck available lookup (pending.getD (.opened [] [])) fields

def sourceStageWithRequiredReader {Other : Type} (previous : Option (WordTaggedObject Other))
    (available : Bool) (lookup : Nat → Option Bool) (fields : List CanonicalScalar) :
    Except Unit (Except BatchError (WordTaggedObject Other)) :=
  sourceOriginalStage previous fields true (sourceReaderFromPrevious previous available lookup)

theorem returned_entire_original_stage_derives_captured_reader_all_input_observations_and_exact_append
    {Other : Type} (previous : Option (WordTaggedObject Other)) (available : Bool)
    (lookup : Nat → Option Bool) (fields : List CanonicalScalar) (object : WordTaggedObject Other)
    (returned : sourceStageWithRequiredReader previous available lookup fields = .ok (.ok object)) :
    sourceOriginalUniqueLoop [] fields = true ∧ available = true ∧
      ∃ ordered members : List CanonicalScalar,
        ((previous = none ∧ ordered = [] ∧ members = []) ∨ previous = some (.inl (.opened ordered members))) ∧
        ordered.length + fields.length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
        fields.all (fun field => !sourceOriginalOrdContains members field) = true ∧
        (∃ flags, TransferBlstArmNullifierReader01.sourceContainsFields available lookup (.opened ordered members) fields = some flags ∧
          flags.length = fields.length) ∧
        (∀ field ∈ fields, lookup (scalarKey field.words) = some false ∧ sourceOriginalOrdContains members field = false) ∧
        object = .inl (.opened (ordered ++ fields) (members ++ fields)) := by
  obtain ⟨unique, ordered, members, prior, capacity, fresh, durable, objectWritten⟩ :=
    TransferBlstArmPending01.returned_original_comparator_stage_derives_all_checks_and_retains_entire_original_fields
      previous fields true (sourceReaderFromPrevious previous available lookup) object returned
  have readerReturned : sourceReaderCheck available lookup (.opened ordered members) fields = .ok () := by
    rcases prior with absent | opened
    · obtain ⟨empty, orderEmpty, membersEmpty⟩ := absent
      subst previous ordered members
      simpa only [if_true, sourceReaderFromPrevious, TransferWordObjectRead01.checkedObject, Option.getD_none] using durable
    · rw [opened] at durable
      simpa only [if_true, sourceReaderFromPrevious, TransferWordObjectRead01.checkedObject, Option.getD_some] using durable
  obtain ⟨gate, flags, observed, width, each⟩ :=
    TransferBlstArmNullifierReader01.returned_original_reader_check_derives_full_vector_and_every_original_input_unspent
      available lookup (.opened ordered members) fields readerReturned
  refine ⟨unique, gate, ordered, members, prior, capacity, fresh, ⟨flags, observed, width⟩, ?_, objectWritten⟩
  intro field inside
  have checked := each field inside
  refine ⟨checked.1, ?_⟩
  rw [TransferBlstArmStage01.original_caller_order_membership_is_exact_qualified_source_membership]
  exact checked.2
set_option pp.all true in
#check @sourceReaderFromPrevious
#print axioms sourceReaderFromPrevious
set_option pp.all true in
#check @sourceStageWithRequiredReader
#print axioms sourceStageWithRequiredReader
set_option pp.all true in
#check @returned_entire_original_stage_derives_captured_reader_all_input_observations_and_exact_append
#print axioms returned_entire_original_stage_derives_captured_reader_all_input_observations_and_exact_append
end ShielddSecurity.TransferBlstArmStageReader01
