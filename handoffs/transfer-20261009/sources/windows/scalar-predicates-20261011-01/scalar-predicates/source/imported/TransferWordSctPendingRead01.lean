import ShielddSecurity.TransferWordObjectPut01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordSctPendingRead01
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferWordObjectRead01 (checkedObject)
/-! Three source SCT pending getters distinguish typed object absence from
Open and Sealed. Outer Except is non-returning type-panic sentinel; inner
Except in ensureSealed is the returned open-block refusal. Absence passes the
source ensure guard while isSealed remains false. Thus ensure success alone
does not prove a present sealed enum. Native Any/Clone/imbl/ownership/compiler
bindings remain explicit; no executed control/native/certification credit. -/

def sourceOrdered {Other : Type} (object : Option (WordTaggedObject Other)) : Except Unit (List CanonicalScalar) :=
  (checkedObject object).map fun pending =>
    match pending with
    | none => []
    | some (.opened ordered _) => ordered
    | some (.sealed ordered) => ordered

def sourceIsSealed {Other : Type} (object : Option (WordTaggedObject Other)) : Except Unit Bool :=
  (checkedObject object).map fun pending =>
    match pending with
    | some (.sealed _) => true
    | _ => false

def sourceEnsureSealed {Other : Type} (object : Option (WordTaggedObject Other)) : Except Unit (Except Unit Unit) :=
  (checkedObject object).map fun pending =>
    match pending with
    | none => .ok ()
    | some (.sealed _) => .ok ()
    | some (.opened _ _) => .error ()

theorem absent_source_pending_returns_empty_vector_false_sealed_and_successful_ensure {Other : Type} :
    sourceOrdered (Other := Other) none = .ok [] ∧ sourceIsSealed (Other := Other) none = .ok false ∧
      sourceEnsureSealed (Other := Other) none = .ok (.ok ()) := ⟨rfl, rfl, rfl⟩

theorem open_source_pending_returns_ordered_vector_and_returned_open_refusal {Other : Type}
    (ordered members : List CanonicalScalar) :
    sourceOrdered (Other := Other) (some (.inl (.opened ordered members))) = .ok ordered ∧
      sourceIsSealed (Other := Other) (some (.inl (.opened ordered members))) = .ok false ∧
      sourceEnsureSealed (Other := Other) (some (.inl (.opened ordered members))) = .ok (.error ()) := ⟨rfl, rfl, rfl⟩

theorem sealed_source_pending_returns_ordered_vector_and_successful_ensure {Other : Type}
    (ordered : List CanonicalScalar) :
    sourceOrdered (Other := Other) (some (.inl (.sealed ordered))) = .ok ordered ∧
      sourceIsSealed (Other := Other) (some (.inl (.sealed ordered))) = .ok true ∧
      sourceEnsureSealed (Other := Other) (some (.inl (.sealed ordered))) = .ok (.ok ()) := ⟨rfl, rfl, rfl⟩

theorem present_wrong_type_panics_before_any_sct_default_or_returned_refusal {Other : Type} (other : Other) :
    sourceOrdered (some (.inr other)) = .error () ∧ sourceIsSealed (some (.inr other)) = .error () ∧
      sourceEnsureSealed (some (.inr other)) = .error () := ⟨rfl, rfl, rfl⟩

theorem source_ensure_success_does_not_imply_a_present_sealed_enum {Other : Type} :
    ∃ object : Option (WordTaggedObject Other), sourceEnsureSealed object = .ok (.ok ()) ∧ sourceIsSealed object = .ok false :=
  ⟨none, rfl, rfl⟩

set_option pp.all true in
#check @sourceOrdered
#print axioms sourceOrdered
set_option pp.all true in
#check @sourceIsSealed
#print axioms sourceIsSealed
set_option pp.all true in
#check @sourceEnsureSealed
#print axioms sourceEnsureSealed
set_option pp.all true in
#check @absent_source_pending_returns_empty_vector_false_sealed_and_successful_ensure
#print axioms absent_source_pending_returns_empty_vector_false_sealed_and_successful_ensure
set_option pp.all true in
#check @open_source_pending_returns_ordered_vector_and_returned_open_refusal
#print axioms open_source_pending_returns_ordered_vector_and_returned_open_refusal
set_option pp.all true in
#check @sealed_source_pending_returns_ordered_vector_and_successful_ensure
#print axioms sealed_source_pending_returns_ordered_vector_and_successful_ensure
set_option pp.all true in
#check @present_wrong_type_panics_before_any_sct_default_or_returned_refusal
#print axioms present_wrong_type_panics_before_any_sct_default_or_returned_refusal
set_option pp.all true in
#check @source_ensure_success_does_not_imply_a_present_sealed_enum
#print axioms source_ensure_success_does_not_imply_a_present_sealed_enum
end ShielddSecurity.TransferWordSctPendingRead01
