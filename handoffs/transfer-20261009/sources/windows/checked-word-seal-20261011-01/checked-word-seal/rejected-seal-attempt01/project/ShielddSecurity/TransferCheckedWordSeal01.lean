import ShielddSecurity.TransferWordStageCachePublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordSeal01
open TransferStateDelta (View Writes overlay Delta)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferWordObjectRead01 (checkedObject)
open TransferWordObjectPut01 (checkedPendingPut pendingTypeMatch)
open TransferWordSctPendingRead01 (sourceOrdered sourceIsSealed sourceEnsureSealed)
open TransferNullifierBatchSource01 (Backend)
open TransferWordStageCachePublication01 (stageAtKey)
/-! Source seal reads the checked selected object, defaults only absence,
rejects already Sealed, and replaces Open with Sealed retaining its original
ordered fields. Outer error denotes non-returning wrong-type panic, inner
error the actual already-sealed refusal. Live functional cache views and
native Any/Clone/imbl/Scalar/compiler/ownership/async bindings are explicit
and OPEN. No native, negative-control, replay or certification credit. -/

def sealFields {Other : Type} (previous : Option (WordTaggedObject Other)) :
    Except Unit (Except Unit (WordTaggedObject Other)) :=
  (checkedObject previous).bind fun pending =>
    match pending with
    | none => (checkedPendingPut previous (.sealed [])).map Except.ok
    | some (.opened ordered _) => (checkedPendingPut previous (.sealed ordered)).map Except.ok
    | some (.sealed _) => .ok (.error ())

def sealAtKey {Other : Type} (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) (key : Nat) :
    Except Unit (Except Unit (Writes (WordTaggedObject Other))) :=
  (sealFields ((overlay parent writes) key)).map
    (fun result => result.map (fun object other => if other = key then some (some object) else writes other))

theorem wrong_type_panics_before_seal_write {Other : Type} (other : Other) :
    sealFields (some (.inr other)) = .error () := rfl

theorem already_sealed_returns_refusal_before_write {Other : Type} (ordered : List CanonicalScalar) :
    sealFields (Other := Other) (some (.inl (.sealed ordered))) = .ok (.error ()) := rfl

theorem absent_defaults_to_empty_then_inserts_sealed {Other : Type} :
    sealFields (Other := Other) none = .ok (.ok (.inl (.sealed []))) := rfl

theorem open_seal_retains_every_original_ordered_field {Other : Type} (ordered members : List CanonicalScalar) :
    sealFields (Other := Other) (some (.inl (.opened ordered members))) = .ok (.ok (.inl (.sealed ordered))) := rfl

theorem returned_seal_derives_actual_prior_absent_or_open_and_exact_original_fields {Other : Type}
    (previous : Option (WordTaggedObject Other)) (object : WordTaggedObject Other)
    (returned : sealFields previous = .ok (.ok object)) :
    ∃ ordered : List CanonicalScalar,
      (previous = none ∧ ordered = [] ∨ ∃ members, previous = some (.inl (.opened ordered members))) ∧
      object = .inl (.sealed ordered) := by
  cases previous with
  | none =>
    exact ⟨[], Or.inl ⟨rfl, rfl⟩, (Except.ok.inj (Except.ok.inj returned)).symm⟩
  | some value =>
    cases value with
    | inr other => cases returned
    | inl pending =>
      cases pending with
      | sealed ordered => cases returned
      | opened ordered members =>
        exact ⟨ordered, Or.inr ⟨members, rfl⟩, (Except.ok.inj (Except.ok.inj returned)).symm⟩

theorem returned_cached_stage_reaches_exact_original_field_seal {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes staged : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (returned : stageAtKey backend child parent writes key inputs = .ok (.ok staged)) :
    ∃ ordered members : List CanonicalScalar,
      sealAtKey parent staged key = .ok (.ok (fun other =>
        if other = key then some (some (.inl (.sealed (ordered ++ inputs)))) else staged other)) ∧
      sourceOrdered (some (Sum.inl (.sealed (ordered ++ inputs)) : WordTaggedObject Other)) = .ok (ordered ++ inputs) ∧
      sourceIsSealed (some (Sum.inl (.sealed (ordered ++ inputs)) : WordTaggedObject Other)) = .ok true ∧
      sourceEnsureSealed (some (Sum.inl (.sealed (ordered ++ inputs)) : WordTaggedObject Other)) = .ok (.ok ()) := by
  obtain ⟨_, ordered, members, _, atKey, _, _⟩ :=
    TransferWordStageCachePublication01.returned_cached_stage_derives_original_fields_checked_getter_and_all_other_key_frames
      backend child parent writes staged key inputs returned
  have selected : (overlay parent staged) key = some (.inl (.opened (ordered ++ inputs) (members ++ inputs))) := by
    simp only [overlay, atKey]
  refine ⟨ordered, members, ?_, rfl, rfl, rfl⟩
  simp only [sealAtKey, selected]
  rfl

set_option pp.all true in
#check @sealFields
#print axioms sealFields
set_option pp.all true in
#check @sealAtKey
#print axioms sealAtKey
set_option pp.all true in
#check @wrong_type_panics_before_seal_write
#print axioms wrong_type_panics_before_seal_write
set_option pp.all true in
#check @already_sealed_returns_refusal_before_write
#print axioms already_sealed_returns_refusal_before_write
set_option pp.all true in
#check @absent_defaults_to_empty_then_inserts_sealed
#print axioms absent_defaults_to_empty_then_inserts_sealed
set_option pp.all true in
#check @open_seal_retains_every_original_ordered_field
#print axioms open_seal_retains_every_original_ordered_field
set_option pp.all true in
#check @returned_seal_derives_actual_prior_absent_or_open_and_exact_original_fields
#print axioms returned_seal_derives_actual_prior_absent_or_open_and_exact_original_fields
set_option pp.all true in
#check @returned_cached_stage_reaches_exact_original_field_seal
#print axioms returned_cached_stage_reaches_exact_original_field_seal
end ShielddSecurity.TransferCheckedWordSeal01
