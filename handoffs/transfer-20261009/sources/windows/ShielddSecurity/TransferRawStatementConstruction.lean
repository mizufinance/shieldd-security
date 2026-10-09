import ShielddSecurity.TransferSemanticConstruction
import ShielddSecurity.TransferSemanticStatementCompletion

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-! Raw legal inputs construct one semantic statement and the original committed
blinding. The SDK conversion retains its global numeric/primitive contracts.
These results do not construct circuit rows or assert decoded Rust correspondence. -/
namespace ShielddSecurity.TransferRawStatementConstruction

open TransferCore TransferSem

def source (c : Crypto) (i : TransferSemanticConstruction.Inputs c) :
    TransferNativeStatementSequence.Source Nat :=
  TransferSemanticStatementCompletion.nativeSource c (TransferSemanticConstruction.construct c i)

def claimed (c : Crypto) (i : TransferSemanticConstruction.Inputs c) : Nat :=
  c.hash .transferStatement (TransferNativeStatementSequence.rustFields (source c i))

theorem source_fields (c : Crypto) (i : TransferSemanticConstruction.Inputs c) :
    TransferNativeStatementSequence.rustFields (source c i) =
      publicFields c (TransferSemanticConstruction.construct c i) :=
  TransferSemanticStatementCompletion.source_public_fields c
    (TransferSemanticConstruction.construct c i)

theorem source_fields_canonical (c : Crypto) (i : TransferSemanticConstruction.Inputs c)
    (canonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    fieldsCanonical (TransferNativeStatementSequence.rustFields (source c i)) :=
  TransferSemanticStatementCompletion.source_public_canonical c
    (TransferSemanticConstruction.construct c i)
    (TransferSemanticConstruction.constructed_transfer_semantics c i canonical group)

theorem claimed_canonical (c : Crypto) (i : TransferSemanticConstruction.Inputs c)
    (canonical : CanonicalCrypto c) : claimed c i < fieldModulus :=
  canonical.1 _ _

theorem constructed_relation_semantics (c : Crypto) (i : TransferSemanticConstruction.Inputs c)
    (canonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    TransferRelationSem c (claimed c i) i.initial.blinding := by
  refine ⟨TransferSemanticConstruction.construct c i,
    TransferSemanticConstruction.constructed_transfer_semantics c i canonical group, ?_, ?_⟩
  · exact (TransferSemanticConstruction.raw_headers_and_selector_preserved c i).2.2.2.2.2.1.symm
  · exact congrArg (c.hash .transferStatement) (source_fields c i)

theorem constructed_full64_conversion {F Sdk Raw Encoded : Type}
    [Field F] [CharP F Scalar.modulus]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : TransferNativeFieldBridge.SdkEncoder Sdk F)
    (numeric : TransferSemanticStatementCompletion.SdkNatConstructor Sdk F sdk)
    (c : Crypto) (i : TransferSemanticConstruction.Inputs c)
    (canonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    ∃ outputs, TransferNativeFieldBridge.fields operations primitives sdk
        ((TransferNativeStatementSequence.rustFields (source c i)).map numeric.ofNat) = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) =
        (TransferNativeStatementSequence.rustFields (source c i)).map (fun n => (n : F)) ∧
      outputs.length = 64 := by
  rw [source_fields]
  exact TransferSemanticStatementCompletion.source_full64_conversion operations primitives sdk numeric c
    (TransferSemanticConstruction.construct c i)
    (TransferSemanticConstruction.constructed_transfer_semantics c i canonical group)

set_option pp.all true in
#check @source_fields
#print axioms source_fields
set_option pp.all true in
#check @source_fields_canonical
#print axioms source_fields_canonical
set_option pp.all true in
#check @claimed_canonical
#print axioms claimed_canonical
set_option pp.all true in
#check @constructed_relation_semantics
#print axioms constructed_relation_semantics
set_option pp.all true in
#check @constructed_full64_conversion
#print axioms constructed_full64_conversion

end ShielddSecurity.TransferRawStatementConstruction
