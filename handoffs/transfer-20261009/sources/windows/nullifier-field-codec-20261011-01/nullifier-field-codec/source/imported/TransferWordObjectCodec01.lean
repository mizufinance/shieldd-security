import ShielddSecurity.TransferCanonicalWordPending01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordObjectCodec01
open TransferCanonicalWordPending01 (WordNativePending encodeWordPending decodeWordPending)
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (nativeSupported)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferFixedFinalizerPublication01 (FinalizationWrites)
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
/-! Concrete heterogeneous object tag contains pending fields represented by
proved source-derived canonical raw Scalar words. Other objects retain a
separate tag, including the known cached tree write. Supported codec and
sealed getter equations derive from field/list proofs, with no caller-supplied
roundtrip. Native Any/downcast/Clone/imbl/private Scalar/compiler/primitive/
Choice/CtOption/full trace/ownership remain explicit. Extended ghost carrier
from the older source model remains; no global erasure/native credit. -/

def WordTaggedObject (Other : Type) : Type := WordNativePending ⊕ Other

def encodeNative {Other : Type} (native : NativePending) : WordTaggedObject Other :=
  .inl (encodeWordPending native)

def decodeNative {Other : Type} : WordTaggedObject Other → NativePending
  | .inl words => decodeWordPending words
  | .inr _ => .opened [] []

def liftWordWrites {Other E A : Type} (writes : OtherFinalizationWrites Other E A) :
    FinalizationWrites (WordTaggedObject Other) E A :=
  ⟨.inr writes.nativeTreeObject, writes.verifiable, writes.nonverifiable, writes.events, writes.queued⟩

theorem supported_word_object_codec_recovers_exact_finite_native_enum {Other : Type}
    (native : NativePending) (supported : nativeSupported native = true) :
    decodeNative (encodeNative (Other := Other) native) = native :=
  TransferCanonicalWordPending01.supported_finite_pending_enum_roundtrips_exact_typed_word_fields native supported

theorem supported_word_object_codec_restores_exact_pending_observations {Other : Type}
    (native : NativePending) (supported : nativeSupported native = true) :
    restore (decodeNative (encodeNative (Other := Other) native)) = restore native :=
  congrArg restore (supported_word_object_codec_recovers_exact_finite_native_enum (Other := Other) native supported)

theorem canonical_bounded_sealed_word_object_getter_recovers_exact_ordered_pending {Other : Type}
    (ordered : List Nat) (capacity : ordered.length ≤ blockCapacity)
    (canonical : ∀ key ∈ ordered, key < nullifierModulus) :
    restore (decodeNative (encodeNative (Other := Other) (.sealed ordered))) = restore (.sealed ordered) := by
  apply supported_word_object_codec_restores_exact_pending_observations (Other := Other)
  simp only [nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨capacity, canonical⟩

theorem empty_word_object_codec_recovers_source_default {Other : Type} :
    decodeNative (encodeNative (Other := Other) (.opened [] [])) = .opened [] [] := rfl

set_option pp.all true in
#check @WordTaggedObject
#print axioms WordTaggedObject
set_option pp.all true in
#check @encodeNative
#print axioms encodeNative
set_option pp.all true in
#check @decodeNative
#print axioms decodeNative
set_option pp.all true in
#check @liftWordWrites
#print axioms liftWordWrites
set_option pp.all true in
#check @supported_word_object_codec_recovers_exact_finite_native_enum
#print axioms supported_word_object_codec_recovers_exact_finite_native_enum
set_option pp.all true in
#check @supported_word_object_codec_restores_exact_pending_observations
#print axioms supported_word_object_codec_restores_exact_pending_observations
set_option pp.all true in
#check @canonical_bounded_sealed_word_object_getter_recovers_exact_ordered_pending
#print axioms canonical_bounded_sealed_word_object_getter_recovers_exact_ordered_pending
set_option pp.all true in
#check @empty_word_object_codec_recovers_source_default
#print axioms empty_word_object_codec_recovers_source_default
end ShielddSecurity.TransferWordObjectCodec01
