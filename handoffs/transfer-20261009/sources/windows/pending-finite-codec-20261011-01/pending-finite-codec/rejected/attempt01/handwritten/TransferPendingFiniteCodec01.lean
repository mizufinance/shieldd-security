import ShielddSecurity.TransferPreparedAcceptedSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPendingFiniteCodec01
open TransferNullifierBatchSource01 (Pending appendPending)
open TransferPendingSetInvariant01 (Coherent)
open TransferPendingSealSource01 (freeze)

/-! Finite erasure/ghost simulation for PendingNullifierBlock. The Open native
set is represented extensionally by a finite member list; its internal order
and duplicates are not observable membership distinctions. Sealed carries
only ordered, and restoration reconstructs its ghost membership from ordered.
Erasure restores a model Pending only when its membership is coherent with
ordered. No codec identity is asserted for arbitrary membership functions.
Native typed object embedding/Clone and finite vector/set/nullifier value
correspondence remain explicit semantic interfaces, independent of hashing.
The observational typed roundtrip compares restored finite enum semantics,
so set ordering or deduplication need not preserve a list representation. -/

inductive NativePending where
  | opened (ordered members : List Nat)
  | sealed (ordered : List Nat)

def restore : NativePending → Pending
  | .opened ordered members => ⟨ordered, fun key => members.contains key, false⟩
  | .sealed ordered => ⟨ordered, fun key => ordered.contains key, true⟩

def erase (pending : Pending) : NativePending :=
  if pending.sealed then .sealed pending.ordered else .opened pending.ordered pending.ordered

def encode {O : Type} (encodeNative : NativePending → O) (pending : Pending) : O := encodeNative (erase pending)

def decode {O : Type} (decodeNative : O → NativePending) (object : O) : Pending := restore (decodeNative object)

theorem restored_membership_has_finite_representation (native : NativePending) :
    ∃ members : List Nat, ∀ key, (restore native).membership key = members.contains key := by
  cases native with
  | opened ordered members => exact ⟨members, fun _ => rfl⟩
  | sealed ordered => exact ⟨ordered, fun _ => rfl⟩

theorem erase_restore_is_order_based_canonicalization (pending : Pending) :
    restore (erase pending) = ⟨pending.ordered, fun key => pending.ordered.contains key, pending.sealed⟩ := by
  cases pending with
  | mk ordered members sealed => cases sealed <;> rfl

theorem coherent_pending_restores_after_erasure (pending : Pending) (coherent : Coherent pending) :
    restore (erase pending) = pending := by
  rw [erase_restore_is_order_based_canonicalization]
  have members : (fun key => pending.ordered.contains key) = pending.membership := funext (fun key => (coherent key).symm)
  rw [members]
  cases pending
  rfl

theorem typed_finite_codec_restores_coherent_pending {O : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (typedRoundtrip : ∀ native, restore (decodeNative (encodeNative native)) = restore native)
    (pending : Pending) (coherent : Coherent pending) :
    decode decodeNative (encode encodeNative pending) = pending := by
  change restore (decodeNative (encodeNative (erase pending))) = pending
  rw [typedRoundtrip]
  exact coherent_pending_restores_after_erasure pending coherent

theorem native_open_append_simulates_model_membership_union (ordered members keys : List Nat) :
    restore (.opened (ordered ++ keys) (members ++ keys)) = appendPending (restore (.opened ordered members)) keys := by
  change (⟨ordered ++ keys, fun key => (members ++ keys).contains key, false⟩ : Pending) =
    ⟨ordered ++ keys, fun key => members.contains key || keys.contains key, false⟩
  have membership : (fun key => (members ++ keys).contains key) = (fun key => members.contains key || keys.contains key) :=
    funext (fun _ => List.contains_append)
  rw [membership]

theorem native_sealed_discards_set_and_restores_frozen_membership (pending : Pending) :
    erase (freeze pending) = .sealed pending.ordered ∧ restore (.sealed pending.ordered) = freeze pending ∧
      Coherent (restore (.sealed pending.ordered)) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

theorem native_default_open_restores_empty_pending :
    restore (.opened [] []) = TransferCurrentPendingReplay01.emptyPending ∧
      erase TransferCurrentPendingReplay01.emptyPending = .opened [] [] := by
  exact ⟨rfl, rfl⟩

set_option pp.all true in
#check @NativePending
#print axioms NativePending
set_option pp.all true in
#check @restore
#print axioms restore
set_option pp.all true in
#check @erase
#print axioms erase
set_option pp.all true in
#check @encode
#print axioms encode
set_option pp.all true in
#check @decode
#print axioms decode
set_option pp.all true in
#check @restored_membership_has_finite_representation
#print axioms restored_membership_has_finite_representation
set_option pp.all true in
#check @erase_restore_is_order_based_canonicalization
#print axioms erase_restore_is_order_based_canonicalization
set_option pp.all true in
#check @coherent_pending_restores_after_erasure
#print axioms coherent_pending_restores_after_erasure
set_option pp.all true in
#check @typed_finite_codec_restores_coherent_pending
#print axioms typed_finite_codec_restores_coherent_pending
set_option pp.all true in
#check @native_open_append_simulates_model_membership_union
#print axioms native_open_append_simulates_model_membership_union
set_option pp.all true in
#check @native_sealed_discards_set_and_restores_frozen_membership
#print axioms native_sealed_discards_set_and_restores_frozen_membership
set_option pp.all true in
#check @native_default_open_restores_empty_pending
#print axioms native_default_open_restores_empty_pending
end ShielddSecurity.TransferPendingFiniteCodec01
