import ShielddSecurity.TransferSymbolicFieldMap01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalWordPending01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarCanonicalKey01 (canonicalScalarForKey)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferPendingFiniteCodec01 (NativePending restore erase)
open TransferBoundedNativeCodec01 (nativeSupported nullifierModulus BoundedPending)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! A concrete finite pending enum with canonical typed raw Scalar words.
Each field is constructed by the proved LE/parser/choice/R2 multiplication
decoder, not by arbitrary desired raw output. Supported keys recover exactly;
unsupported Nat values wrap modulo p and receive no roundtrip claim. The seen
set remains an extensional finite member list as in the original pending
model. Native imbl containers, Clone/Any/private Scalar/compiler/full trace
bindings remain explicit; this derives a field-codec model contract only. -/

def encodeWordScalar (key : Nat) : CanonicalScalar :=
  canonicalScalarForKey ⟨key % nullifierModulus, Nat.mod_lt key (by decide)⟩

inductive WordNativePending where
  | opened (ordered members : List CanonicalScalar)
  | sealed (ordered : List CanonicalScalar)

def encodeWordPending : NativePending → WordNativePending
  | .opened ordered members => .opened (ordered.map encodeWordScalar) (members.map encodeWordScalar)
  | .sealed ordered => .sealed (ordered.map encodeWordScalar)

def decodeWordPending : WordNativePending → NativePending
  | .opened ordered members => .opened (ordered.map (fun scalar => scalarKey scalar.words)) (members.map (fun scalar => scalarKey scalar.words))
  | .sealed ordered => .sealed (ordered.map (fun scalar => scalarKey scalar.words))

theorem constructed_word_scalar_projects_to_source_key_modulo_field (key : Nat) :
    scalarKey (encodeWordScalar key).words = key % nullifierModulus :=
  TransferScalarCanonicalKey01.constructed_source_scalar_projects_to_exact_canonical_key
    ⟨key % nullifierModulus, Nat.mod_lt key (by decide)⟩

theorem canonical_key_list_roundtrips_through_actual_modeled_word_fields
    (keys : List Nat) (canonical : ∀ key ∈ keys, key < nullifierModulus) :
    (keys.map encodeWordScalar).map (fun scalar => scalarKey scalar.words) = keys := by
  exact TransferSymbolicFieldMap01.finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse
    encodeWordScalar (fun scalar => scalarKey scalar.words) keys
    (fun key inside => (constructed_word_scalar_projects_to_source_key_modulo_field key).trans
      (Nat.mod_eq_of_lt (canonical key inside)))

theorem supported_finite_pending_enum_roundtrips_exact_typed_word_fields
    (native : NativePending) (supported : nativeSupported native = true) :
    decodeWordPending (encodeWordPending native) = native := by
  cases native with
  | opened ordered members =>
    simp only [nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at supported
    change NativePending.opened ((ordered.map encodeWordScalar).map (fun scalar => scalarKey scalar.words))
      ((members.map encodeWordScalar).map (fun scalar => scalarKey scalar.words)) = NativePending.opened ordered members
    rw [canonical_key_list_roundtrips_through_actual_modeled_word_fields ordered supported.1.2,
      canonical_key_list_roundtrips_through_actual_modeled_word_fields members supported.2]
  | sealed ordered =>
    simp only [nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at supported
    change NativePending.sealed ((ordered.map encodeWordScalar).map (fun scalar => scalarKey scalar.words)) = NativePending.sealed ordered
    rw [canonical_key_list_roundtrips_through_actual_modeled_word_fields ordered supported.2]

theorem coherent_bounded_current_pending_restores_from_constructed_word_codec
    (pending : TransferNullifierBatchSource01.Pending)
    (coherent : TransferPendingSetInvariant01.Coherent pending)
    (capacity : pending.ordered.length ≤ blockCapacity) (canonical : BoundedPending pending) :
    restore (decodeWordPending (encodeWordPending (erase pending))) = pending := by
  have supported := TransferBoundedNativeCodec01.bounded_consensus_pending_erases_to_supported_finite_native_domain pending capacity canonical
  rw [supported_finite_pending_enum_roundtrips_exact_typed_word_fields (erase pending) supported]
  exact TransferPendingFiniteCodec01.coherent_pending_restores_after_erasure pending coherent

set_option pp.all true in
#check @encodeWordScalar
#print axioms encodeWordScalar
set_option pp.all true in
#check @WordNativePending
#print axioms WordNativePending
set_option pp.all true in
#check @encodeWordPending
#print axioms encodeWordPending
set_option pp.all true in
#check @decodeWordPending
#print axioms decodeWordPending
set_option pp.all true in
#check @constructed_word_scalar_projects_to_source_key_modulo_field
#print axioms constructed_word_scalar_projects_to_source_key_modulo_field
set_option pp.all true in
#check @canonical_key_list_roundtrips_through_actual_modeled_word_fields
#print axioms canonical_key_list_roundtrips_through_actual_modeled_word_fields
set_option pp.all true in
#check @supported_finite_pending_enum_roundtrips_exact_typed_word_fields
#print axioms supported_finite_pending_enum_roundtrips_exact_typed_word_fields
set_option pp.all true in
#check @coherent_bounded_current_pending_restores_from_constructed_word_codec
#print axioms coherent_bounded_current_pending_restores_from_constructed_word_codec
end ShielddSecurity.TransferCanonicalWordPending01
