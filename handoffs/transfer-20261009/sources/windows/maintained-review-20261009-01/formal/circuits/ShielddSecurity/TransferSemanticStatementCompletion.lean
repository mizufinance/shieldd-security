import ShielddSecurity.TransferSem
import ShielddSecurity.TransferNativeStatementSequence

set_option maxHeartbeats 400000

/-! Original semantic witness -> native structured source construction.
All fields are selected independently from witness members and semantic balance;
no sequence equality, statement hash equation or result semantics is a premise. -/
namespace ShielddSecurity.TransferSemanticStatementCompletion

def nativePoint (p : TransferCore.Affine) : TransferNativeStatementSequence.Point Nat := ⟨p.x,p.y⟩
def nativeOutput (o : TransferSem.Output) : TransferNativeStatementSequence.Output Nat := ⟨o.noteCommitment,o.recovery.commitment⟩
def nativeCore (t : TransferSem.Tier) : TransferNativeStatementSequence.Core Nat :=
  ⟨nativePoint t.epk,t.c2,t.ciphertext 0,t.confirmation⟩
def nativeExtended (t : TransferSem.Tier) : TransferNativeStatementSequence.Extended Nat :=
  ⟨nativePoint t.epk,t.c2,t.ciphertext 0,t.ciphertext 1,t.ciphertext 2⟩
def nativeOwnership (o : TransferSem.Ownership) : TransferNativeStatementSequence.Ownership Nat :=
  ⟨nativePoint o.r,nativePoint o.c⟩

def nativeSource (c : TransferSem.Crypto) (w : TransferSem.Witness) : TransferNativeStatementSequence.Source Nat :=
  { rk := nativePoint w.auth.rk
    anchor := w.anchor
    outputs := ⟨nativeOutput (w.outputs 0),nativeOutput (w.outputs 1)⟩
    balance := nativePoint (TransferSem.balance c w)
    routingTags := ⟨w.routing.tags 0,w.routing.tags 1⟩
    routingParameter := w.routing.parameterSet
    volume := ⟨w.volume.nullifier,w.volume.commitment,w.volume.dayStart,w.volume.context⟩
    spends := ⟨(w.spends 0).nullifier,(w.spends 1).nullifier⟩
    assetAnchor := w.assetAnchor
    complianceAnchor := w.userAnchor
    timestamp := w.timestamp
    audit := {
      detection := ⟨w.encryption.detection 0,w.encryption.detection 1,
        w.encryption.detection 2,w.encryption.detection 3⟩
      senderCore := nativeCore (w.encryption.tiers 0)
      senderExt := nativeExtended (w.encryption.tiers 1)
      outputCore := nativeCore (w.encryption.tiers 2)
      outputExt := nativeExtended (w.encryption.tiers 3)
      policy := ⟨w.encryption.policy 0,w.encryption.policy 1,
        w.encryption.policy 2,w.encryption.policy 3⟩
      salts := ⟨w.encryption.salts 0,w.encryption.salts 1,
        w.encryption.salts 2,w.encryption.salts 3⟩
      auditEpoch := w.encryption.auditEpoch
      ownership := ⟨nativeOwnership (w.encryption.ownership 0),
        nativeOwnership (w.encryption.ownership 1)⟩ } }

theorem source_public_fields (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    TransferNativeStatementSequence.rustFields (nativeSource c w) = TransferSem.publicFields c w := by rfl

theorem source_public_canonical (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    TransferSem.fieldsCanonical (TransferNativeStatementSequence.rustFields (nativeSource c w)) := by
  rw [source_public_fields]
  exact legal.2.2

def mapPoint {A B : Type} (f : A → B) (p : TransferNativeStatementSequence.Point A) :
    TransferNativeStatementSequence.Point B := ⟨f p.x,f p.y⟩
def mapOutput {A B : Type} (f : A → B) (o : TransferNativeStatementSequence.Output A) :
    TransferNativeStatementSequence.Output B := ⟨f o.note,f o.recovery⟩
def mapCore {A B : Type} (f : A → B) (t : TransferNativeStatementSequence.Core A) :
    TransferNativeStatementSequence.Core B := ⟨mapPoint f t.epk,f t.c2,f t.ciphertext,f t.confirmation⟩
def mapExtended {A B : Type} (f : A → B) (t : TransferNativeStatementSequence.Extended A) :
    TransferNativeStatementSequence.Extended B :=
  ⟨mapPoint f t.epk,f t.c2,f t.ciphertext.1,f t.ciphertext.2.1,f t.ciphertext.2.2⟩
def mapOwnership {A B : Type} (f : A → B) (o : TransferNativeStatementSequence.Ownership A) :
    TransferNativeStatementSequence.Ownership B := ⟨mapPoint f o.r,mapPoint f o.c⟩

def mapSource {A B : Type} (f : A → B) (s : TransferNativeStatementSequence.Source A) :
    TransferNativeStatementSequence.Source B :=
  { rk := mapPoint f s.rk
    anchor := f s.anchor
    outputs := ⟨mapOutput f s.outputs.1,mapOutput f s.outputs.2⟩
    balance := mapPoint f s.balance
    routingTags := ⟨f s.routingTags.1,f s.routingTags.2⟩
    routingParameter := f s.routingParameter
    volume := ⟨f s.volume.nullifier,f s.volume.commitment,f s.volume.dayStart,f s.volume.context⟩
    spends := ⟨f s.spends.1,f s.spends.2⟩
    assetAnchor := f s.assetAnchor
    complianceAnchor := f s.complianceAnchor
    timestamp := f s.timestamp
    audit := {
      detection := ⟨f s.audit.detection.1,f s.audit.detection.2.1,
        f s.audit.detection.2.2.1,f s.audit.detection.2.2.2⟩
      senderCore := mapCore f s.audit.senderCore
      senderExt := mapExtended f s.audit.senderExt
      outputCore := mapCore f s.audit.outputCore
      outputExt := mapExtended f s.audit.outputExt
      policy := ⟨f s.audit.policy.ringId,f s.audit.policy.policyId,
        f s.audit.policy.resource,f s.audit.policy.permission⟩
      salts := ⟨f s.audit.salts.1,f s.audit.salts.2.1,f s.audit.salts.2.2.1,f s.audit.salts.2.2.2⟩
      auditEpoch := f s.audit.auditEpoch
      ownership := ⟨mapOwnership f s.audit.ownership.1,mapOwnership f s.audit.ownership.2⟩ } }

theorem mapped_source_fields {A B : Type} (f : A → B) (s : TransferNativeStatementSequence.Source A) :
    TransferNativeStatementSequence.rustFields (mapSource f s) =
      (TransferNativeStatementSequence.rustFields s).map f := by
  simp only [mapSource, mapPoint, mapOutput, mapCore, mapExtended, mapOwnership,
    TransferNativeStatementSequence.rustFields, TransferNativeStatementSequence.pointFields,
    TransferNativeStatementSequence.outputFields, TransferNativeStatementSequence.coreFields,
    TransferNativeStatementSequence.extendedFields, TransferNativeStatementSequence.ownershipFields,
    List.map_append, List.map_cons, List.map_nil]

/-- Global SDK numeric constructor contract, independent of any action/hash:
 every canonical natural representative becomes an SDK object with that value.
 Encoding and BLST byte primitives retain their existing named contracts. -/
structure SdkNatConstructor (Sdk F : Type) [Field F]
    (sdk : TransferNativeFieldBridge.SdkEncoder Sdk F) where
  ofNat : Nat → Sdk
  value : ∀ n, n < TransferCore.fieldModulus → sdk.value (ofNat n) = (n : F)

theorem field_modulus_matches_codec : TransferCore.fieldModulus = Scalar.modulus := by rfl

theorem source_full64_conversion {F Sdk Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : TransferNativeFieldBridge.SdkEncoder Sdk F) (numeric : SdkNatConstructor Sdk F sdk)
    (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem c w) :
    ∃ outputs, TransferNativeFieldBridge.fields operations primitives sdk
        ((TransferSem.publicFields c w).map numeric.ofNat) = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) =
        (TransferSem.publicFields c w).map (fun n => (n : F)) ∧ outputs.length = 64 := by
  obtain ⟨outputs, read, meaning, count⟩ :=
    TransferNativeStatementSequence.source_sequence_conversion operations primitives sdk
      (mapSource numeric.ofNat (nativeSource c w))
  rw [mapped_source_fields, source_public_fields] at read meaning
  refine ⟨outputs,read,?_,count⟩
  rw [meaning, List.map_map]
  apply List.map_congr_left
  intro n member
  exact numeric.value n (legal.2.2 n member)

#print axioms field_modulus_matches_codec
#print axioms mapped_source_fields
#print axioms source_full64_conversion

#print axioms source_public_fields
#print axioms source_public_canonical
end ShielddSecurity.TransferSemanticStatementCompletion
