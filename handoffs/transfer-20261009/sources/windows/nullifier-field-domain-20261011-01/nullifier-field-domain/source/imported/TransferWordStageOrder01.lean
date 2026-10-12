import ShielddSecurity.TransferCanonicalSourceMembership01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordStageOrder01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferWordObjectRead01 (checkedObject)
open TransferWordObjectPut01 (checkedPendingPut)
open TransferNullifierBatchSource01 (BatchError uniqueLoop)
open TransferCanonicalSourceMembership01 (sourceOrdContains)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Pinned stage_nullifiers control order with canonical original fields.
Local uniqueness is checked before typed object access. Absence defaults Open;
Sealed refuses; source capacity and pending-membership checks precede the
optional durable reader interface and one guarded typed put. Original vectors
are appended without key-to-word reconstruction. Outer error is non-returning
type panic; inner error is returned batch refusal. The reader parameter owns
fallible durable-vector/zip-unspent semantics. Native BTreeSet/imbl/Any/Clone,
private Scalar/usize/compiler/async/state binding remain OPEN. Source model
only; no native/control/certification credit. -/

def admitOpen (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) : Except BatchError Unit :=
  if TransferPendingSaturatingCapacity01.sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤ blockCapacity then
    if inputs.all (fun scalar => !sourceOrdContains members scalar) then
      if checkDurable then reader inputs else .ok ()
    else .error .pending
  else .error .capacity

def appendAfterCheckedRead {Other : Type} (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) : Except Unit (Except BatchError (WordTaggedObject Other)) :=
  match checkedObject previous with
  | .error panic => .error panic
  | .ok pending =>
    match pending.getD (.opened [] []) with
    | .sealed _ => .ok (.error .sealed)
    | .opened ordered members =>
      match admitOpen ordered members inputs checkDurable reader with
      | .error refusal => .ok (.error refusal)
      | .ok _ => (checkedPendingPut previous (.opened (ordered ++ inputs) (members ++ inputs))).map Except.ok

def stageFields {Other : Type} (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) : Except Unit (Except BatchError (WordTaggedObject Other)) :=
  if uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) then
    appendAfterCheckedRead previous inputs checkDurable reader
  else .ok (.error .duplicate)

theorem duplicate_refusal_precedes_even_wrong_type_object_access {Other : Type} (other : Other)
    (inputs : List CanonicalScalar) (checkDurable : Bool) (reader : List CanonicalScalar → Except BatchError Unit)
    (duplicate : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = false) :
    stageFields (some (.inr other)) inputs checkDurable reader = .ok (.error .duplicate) := by
  simp only [stageFields, duplicate, Bool.false_eq_true, if_false]

theorem unique_batch_wrong_type_panics_before_any_returned_staging_refusal {Other : Type} (other : Other)
    (inputs : List CanonicalScalar) (checkDurable : Bool) (reader : List CanonicalScalar → Except BatchError Unit)
    (unique : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true) :
    stageFields (some (.inr other)) inputs checkDurable reader = .error () := by
  simp only [stageFields, unique, if_true, appendAfterCheckedRead, checkedObject]

theorem unique_batch_sealed_object_returns_sealed_refusal_before_admission {Other : Type}
    (ordered inputs : List CanonicalScalar) (checkDurable : Bool) (reader : List CanonicalScalar → Except BatchError Unit)
    (unique : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true) :
    stageFields (Other := Other) (some (.inl (.sealed ordered))) inputs checkDurable reader = .ok (.error .sealed) := by
  simp only [stageFields, unique, if_true, appendAfterCheckedRead, checkedObject, Option.getD_some]

theorem admitted_open_append_writes_exact_original_ordered_and_member_fields {Other : Type}
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool) (reader : List CanonicalScalar → Except BatchError Unit)
    (unique : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true)
    (admitted : admitOpen ordered members inputs checkDurable reader = .ok ()) :
    stageFields (Other := Other) (some (.inl (.opened ordered members))) inputs checkDurable reader =
      .ok (.ok (.inl (.opened (ordered ++ inputs) (members ++ inputs)))) := by
  simp only [stageFields, unique, if_true, appendAfterCheckedRead, checkedObject, Option.getD_some, admitted]
  rfl

theorem absent_object_defaults_open_and_admitted_append_retains_original_fields {Other : Type}
    (inputs : List CanonicalScalar) (checkDurable : Bool) (reader : List CanonicalScalar → Except BatchError Unit)
    (unique : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true)
    (admitted : admitOpen [] [] inputs checkDurable reader = .ok ()) :
    stageFields (Other := Other) none inputs checkDurable reader = .ok (.ok (.inl (.opened inputs inputs))) := by
  simp only [stageFields, unique, if_true, appendAfterCheckedRead, checkedObject, Option.getD_none, admitted, List.nil_append]
  rfl

set_option pp.all true in
#check @admitOpen
#print axioms admitOpen
set_option pp.all true in
#check @appendAfterCheckedRead
#print axioms appendAfterCheckedRead
set_option pp.all true in
#check @stageFields
#print axioms stageFields
set_option pp.all true in
#check @duplicate_refusal_precedes_even_wrong_type_object_access
#print axioms duplicate_refusal_precedes_even_wrong_type_object_access
set_option pp.all true in
#check @unique_batch_wrong_type_panics_before_any_returned_staging_refusal
#print axioms unique_batch_wrong_type_panics_before_any_returned_staging_refusal
set_option pp.all true in
#check @unique_batch_sealed_object_returns_sealed_refusal_before_admission
#print axioms unique_batch_sealed_object_returns_sealed_refusal_before_admission
set_option pp.all true in
#check @admitted_open_append_writes_exact_original_ordered_and_member_fields
#print axioms admitted_open_append_writes_exact_original_ordered_and_member_fields
set_option pp.all true in
#check @absent_object_defaults_open_and_admitted_append_retains_original_fields
#print axioms absent_object_defaults_open_and_admitted_append_retains_original_fields
end ShielddSecurity.TransferWordStageOrder01
