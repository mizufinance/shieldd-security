import ShielddSecurity.TransferScalarByteEquality01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSourceTypedInputProjection01
open TransferWholeReaderRefusal01 (Config)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact all-slot source-shaped map of Transfer input nullifier fields, followed
by the finite four-word scalar serializer. Concrete configuration installation
derives typed input projection and canonical key bounds; every slot is kept
in source order, without a caller-provided desired key vector/range premise.
Action-input and nullifier-word selectors describe the actual runtime binding
interface. Checked pinned source accessor/iterator/batch/byte-forwarding shape
does not prove Rust/native iterator/field/Scalar/codec/compiler trace semantics. -/

def typedWords {I A : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) : List (Vector UInt64 4) :=
  (inputs action).map wordOf

def sourceKeys {I A : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) : List Nat :=
  (inputs action).map (fun input => scalarKey (wordOf input))

def installTypedInputs {O E K X Tree A I : Type} (config : Config O E K X Tree A)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) : Config O E K X Tree A :=
  {config with inputs := sourceKeys inputs wordOf}

theorem installed_config_inputs_are_exact_ordered_typed_scalar_projection {O E K X Tree A I : Type}
    (config : Config O E K X Tree A) (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    (installTypedInputs config inputs wordOf).inputs action = (typedWords inputs wordOf action).map scalarKey := by
  change (inputs action).map (fun input => scalarKey (wordOf input)) = ((inputs action).map wordOf).map scalarKey
  rw [List.map_map]
  simp only [Function.comp_def]

theorem source_keys_are_exact_ordered_mathematical_montgomery_values {I A : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    sourceKeys inputs wordOf action = (inputs action).map (fun input => montgomeryValue (wordOf input)) := by
  exact List.map_congr_left (fun input _ =>
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value (wordOf input))

theorem installed_config_derives_every_input_key_in_canonical_nullifier_domain {O E K X Tree A I : Type}
    (config : Config O E K X Tree A) (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    ∀ key ∈ (installTypedInputs config inputs wordOf).inputs action, key < nullifierModulus := by
  intro key inside
  change key ∈ (inputs action).map (fun input => scalarKey (wordOf input)) at inside
  obtain ⟨input, _, projected⟩ := List.mem_map.mp inside
  rw [← projected]
  exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical (wordOf input)

set_option pp.all true in
#check @typedWords
#print axioms typedWords
set_option pp.all true in
#check @sourceKeys
#print axioms sourceKeys
set_option pp.all true in
#check @installTypedInputs
#print axioms installTypedInputs
set_option pp.all true in
#check @installed_config_inputs_are_exact_ordered_typed_scalar_projection
#print axioms installed_config_inputs_are_exact_ordered_typed_scalar_projection
set_option pp.all true in
#check @source_keys_are_exact_ordered_mathematical_montgomery_values
#print axioms source_keys_are_exact_ordered_mathematical_montgomery_values
set_option pp.all true in
#check @installed_config_derives_every_input_key_in_canonical_nullifier_domain
#print axioms installed_config_derives_every_input_key_in_canonical_nullifier_domain
end ShielddSecurity.TransferSourceTypedInputProjection01
