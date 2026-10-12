import ShielddSecurity.TransferNativeSealTransfer01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativePendingWrite01
open TransferStateDelta TransferNullifierBatchSource01
open TransferPendingFiniteCodec01 (NativePending erase)
open TransferPendingSetInvariant01 (Invariant Coherent)
open TransferBoundedNativeCodec01 (BoundedPending nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)

/-! Primitive pending writes, independently of subsequent raw-body success.
The actual modeled inspection derives the next coherent bounded pending value.
Only encoding such supported coherent values is a native correspondence
premise. There is no obligation on unsupported ghost values, no assumption
that a later note/SCT/raw body succeeds, and no claim that a failed child is
published. Native pending getter, finite collection/Clone/typed object, byte
projection, actual trace, ownership/locks/reader/OS remain interfaces. -/

theorem successful_primitive_inspection_derives_supported_native_next {O E : Type}
    (backend : Backend O E) (wordMax : Nat) (child : Delta O E) (keys : List Nat) (next : Pending)
    (initial : Invariant blockCapacity (backend.pending child))
    (bounded : BoundedPending (backend.pending child))
    (inputs : ∀ key ∈ keys, key < nullifierModulus) (belowWord : blockCapacity < wordMax)
    (checked : inspect backend wordMax blockCapacity child keys = .ok next) :
    Invariant blockCapacity next ∧ BoundedPending next ∧ nativeSupported (erase next) = true := by
  have nextInvariant := TransferPendingSetInvariant01.successful_inspection_preserves_invariant
    backend wordMax blockCapacity child keys next initial.1 initial.2.1 belowWord checked
  have ordered := (inspection_success_capacity_and_all_inputs backend wordMax blockCapacity child keys next belowWord checked).1
  have nextBounded : BoundedPending next := by
    intro key inside
    rw [ordered] at inside
    cases List.mem_append.mp inside with
    | inl earlier => exact bounded key earlier
    | inr current => exact inputs key current
  exact ⟨nextInvariant, nextBounded,
    TransferBoundedNativeCodec01.bounded_consensus_pending_erases_to_supported_finite_native_domain
      next nextInvariant.2.2.1 nextBounded⟩

theorem successful_nonempty_primitive_writes_actual_supported_native_object {O E : Type}
    (encodeNative : NativePending → O) (backend : Backend O E)
    (nativeEncoding : ∀ pending, Coherent pending → pending.ordered.length ≤ blockCapacity →
      BoundedPending pending → backend.encode pending = encodeNative (erase pending))
    (wordMax objectKey : Nat) (sourceHasId : Bool) (child : Delta O E) (keys : List Nat) (cache : Cache O E)
    (initial : Invariant blockCapacity (backend.pending child))
    (bounded : BoundedPending (backend.pending child))
    (inputs : ∀ key ∈ keys, key < nullifierModulus) (belowWord : blockCapacity < wordMax)
    (nonempty : keys.isEmpty = false)
    (success : executeNullify backend wordMax blockCapacity objectKey sourceHasId child keys = ⟨cache, .ok ()⟩) :
    sourceHasId = true ∧ ∃ (next : Pending),
      inspect backend wordMax blockCapacity child keys = .ok next ∧
      Invariant blockCapacity next ∧ BoundedPending next ∧ nativeSupported (erase next) = true ∧
      cache = (putObject child objectKey (some (encodeNative (erase next)))).cache ∧
      (applyCache child.parent cache).objects objectKey = some (encodeNative (erase next)) := by
  obtain ⟨source, next, checked, cacheEq⟩ := successful_nonempty_batch_single_object_write
    backend wordMax blockCapacity objectKey sourceHasId child keys cache nonempty success
  have derived := successful_primitive_inspection_derives_supported_native_next
    backend wordMax child keys next initial bounded inputs belowWord checked
  have encoded := nativeEncoding next derived.1.1 derived.1.2.2.1 derived.2.1
  rw [encoded] at cacheEq
  refine ⟨source, next, checked, derived.1, derived.2.1, derived.2.2, cacheEq, ?_⟩
  rw [cacheEq]
  exact object_write_visible_in_child child objectKey (some (encodeNative (erase next)))

theorem every_modeled_primitive_branch_retains_cache_or_writes_supported_native {O E : Type}
    (encodeNative : NativePending → O) (backend : Backend O E)
    (nativeEncoding : ∀ pending, Coherent pending → pending.ordered.length ≤ blockCapacity →
      BoundedPending pending → backend.encode pending = encodeNative (erase pending))
    (wordMax objectKey : Nat) (sourceHasId : Bool) (child : Delta O E) (keys : List Nat)
    (initial : Invariant blockCapacity (backend.pending child))
    (bounded : BoundedPending (backend.pending child))
    (inputs : ∀ key ∈ keys, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    (executeNullify backend wordMax blockCapacity objectKey sourceHasId child keys).cache = child.cache ∨
      ∃ (next : Pending), inspect backend wordMax blockCapacity child keys = .ok next ∧
        nativeSupported (erase next) = true ∧
        executeNullify backend wordMax blockCapacity objectKey sourceHasId child keys =
          ⟨(putObject child objectKey (some (encodeNative (erase next)))).cache, .ok ()⟩ := by
  cases empty : keys.isEmpty with
  | true => left; simp only [executeNullify, empty, if_true]
  | false =>
    cases sourceHasId with
    | false => left; simp only [executeNullify, empty, Bool.false_eq_true, if_false]
    | true =>
      cases checked : inspect backend wordMax blockCapacity child keys with
      | error error => left; simp only [executeNullify, empty, Bool.false_eq_true, if_false, if_true, checked]
      | ok next =>
        have derived := successful_primitive_inspection_derives_supported_native_next
          backend wordMax child keys next initial bounded inputs belowWord checked
        have encoded := nativeEncoding next derived.1.1 derived.1.2.2.1 derived.2.1
        right
        refine ⟨next, rfl, derived.2.2, ?_⟩
        simp only [executeNullify, empty, Bool.false_eq_true, if_false, if_true, checked, encoded]

set_option pp.all true in
#check @successful_primitive_inspection_derives_supported_native_next
#print axioms successful_primitive_inspection_derives_supported_native_next
set_option pp.all true in
#check @successful_nonempty_primitive_writes_actual_supported_native_object
#print axioms successful_nonempty_primitive_writes_actual_supported_native_object
set_option pp.all true in
#check @every_modeled_primitive_branch_retains_cache_or_writes_supported_native
#print axioms every_modeled_primitive_branch_retains_cache_or_writes_supported_native
end ShielddSecurity.TransferNativePendingWrite01
