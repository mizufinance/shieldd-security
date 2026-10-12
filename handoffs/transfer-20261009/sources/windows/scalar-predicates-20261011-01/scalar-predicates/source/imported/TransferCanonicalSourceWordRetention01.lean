import ShielddSecurity.TransferWordSctPendingRead01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalSourceWordRetention01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
attribute [local irreducible] TransferScalarCanonicalKey01.canonicalScalarForKey
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (encodeWordScalar)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarCanonicalKey01 (canonicalScalarForKey)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Canonical typed source inputs retain their raw word vectors when passing
through mathematical key projection and the constructed LE/R2 field codec.
The packed raw <p invariant belongs to the input type; arbitrary raw vectors
and noncanonical aliases receive no identity claim. Native private Scalar
invariant/constructor/compiler/selector bindings remain explicit. No caller
codec inverse or chosen output is supplied, and no native/control/cert credit. -/

theorem source_key_word_encoder_recovers_original_canonical_raw_vector (scalar : CanonicalScalar) :
    (encodeWordScalar (scalarKey scalar.words)).words = scalar.words := by
  let key : Fin nullifierModulus := ⟨scalarKey scalar.words,
    TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words⟩
  have sameKey : (⟨scalarKey scalar.words % nullifierModulus,
      Nat.mod_lt (scalarKey scalar.words) (by decide)⟩ : Fin nullifierModulus) = key :=
    Fin.ext (Nat.mod_eq_of_lt key.isLt)
  have inverse := TransferScalarCanonicalKey01.canonical_source_key_constructor_recovers_every_canonical_raw_vector scalar
  change (canonicalScalarForKey ⟨scalarKey scalar.words % nullifierModulus,
    Nat.mod_lt (scalarKey scalar.words) (by decide)⟩).words = scalar.words
  exact (congrArg (fun value : Fin nullifierModulus => (canonicalScalarForKey value).words) sameKey).trans inverse

theorem source_key_word_encoder_recovers_entire_canonical_typed_scalar (scalar : CanonicalScalar) :
    encodeWordScalar (scalarKey scalar.words) = scalar := by
  have words := source_key_word_encoder_recovers_original_canonical_raw_vector scalar
  cases scalar with
  | mk raw canonical =>
    generalize encoded : encodeWordScalar (scalarKey raw) = output at words ⊢
    cases output with
    | mk next bound =>
      have same : next = raw := words
      cases same
      rfl

theorem canonical_source_scalar_list_recovers_exact_ordered_original_fields (source : List CanonicalScalar) :
    (source.map (fun scalar => scalarKey scalar.words)).map encodeWordScalar = source :=
  TransferSymbolicFieldMap01.finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse
    (fun scalar : CanonicalScalar => scalarKey scalar.words) encodeWordScalar source
    (fun scalar _ => source_key_word_encoder_recovers_entire_canonical_typed_scalar scalar)

set_option pp.all true in
#check @source_key_word_encoder_recovers_original_canonical_raw_vector
#print axioms source_key_word_encoder_recovers_original_canonical_raw_vector
set_option pp.all true in
#check @source_key_word_encoder_recovers_entire_canonical_typed_scalar
#print axioms source_key_word_encoder_recovers_entire_canonical_typed_scalar
set_option pp.all true in
#check @canonical_source_scalar_list_recovers_exact_ordered_original_fields
#print axioms canonical_source_scalar_list_recovers_exact_ordered_original_fields
end ShielddSecurity.TransferCanonicalSourceWordRetention01
