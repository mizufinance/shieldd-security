import ShielddSecurity.ShielddNativeRegulatedLegality
import ShielddSecurity.ShielddNativeRegisteredNullifier

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeActionWitnessAssociation

open ShielddNativeAddress ShielddNativeAddressLegality TransferNativeRegulatedSource

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

structure Sender (S Q : Type) where
  address : Address S
  dhBase : S
  registered : Q

/-- The same owned ActionWitness fields passed through transfer_public_private
and pari::compliance. This record retains the sender's independently stored
commitment; it is never chosen from the derived RNK/hash output. -/
structure Source (S Q Routes Origin Key : Type) where
  asset : Q
  regulated : Bool
  assetLeaf : Leaf Q S (ShielddNativeRegulatedLegality.AuditKeys S)
  sender : Sender S Q
  policy : Option (Policy S Routes Origin (ShielddNativeRegulatedLegality.AuditKeys S) Key)

noncomputable def nullifierKey [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : Source S Q Routes Origin Key) : Option Q :=
  ShielddNativeRegisteredNullifier.nullifierKey walletNk source.regulated source.policy
    (fun policy => ShielddNativeRegulatedLegality.deriveRegulated upstream primitives agreement hash
      secret source.sender.address source.asset policy.ring.ringKey source.sender.dhBase)
    (fun key => hash 18 [key]) source.sender.registered

theorem callback_arguments [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : Source S Q Routes Origin Key) :
    nullifierKey upstream primitives agreement hash secret walletNk source =
      ShielddNativeRegisteredNullifier.nullifierKey walletNk source.regulated source.policy
        (fun policy => ShielddNativeRegulatedLegality.deriveRegulated upstream primitives agreement hash
          secret source.sender.address source.asset policy.ring.ringKey source.sender.dhBase)
        (fun key => hash 18 [key]) source.sender.registered := rfl

theorem accepted_regulated [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : Source S Q Routes Origin Key) (key : Q)
    (regulated : source.regulated = true)
    (accepted : nullifierKey upstream primitives agreement hash secret walletNk source = some key) :
    ∃ policy, source.policy = some policy ∧
      ShielddNativeRegulatedLegality.deriveRegulated upstream primitives agreement hash
        secret source.sender.address source.asset policy.ring.ringKey source.sender.dhBase = some key ∧
      hash 18 [key] = source.sender.registered ∧
      LegalPoint upstream policy.ring.ringKey ∧ LegalPoint upstream source.sender.dhBase := by
  unfold nullifierKey at accepted
  rw [regulated] at accepted
  obtain ⟨policy,present,derived,matching⟩ := ShielddNativeRegisteredNullifier.regulated_value
    walletNk source.policy _ (fun key => hash 18 [key]) source.sender.registered key accepted
  have legal := ShielddNativeRegulatedLegality.regulated_derivation_legal upstream primitives
    agreement hash secret source.sender.address source.asset policy.ring.ringKey source.sender.dhBase key derived
  exact ⟨policy,present,derived,matching,legal.1,legal.2⟩

theorem accepted_views [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : Source S Q Routes Origin Key) (key : Q)
    (regulated : source.regulated = true)
    (accepted : nullifierKey upstream primitives agreement hash secret walletNk source = some key) :
    LegalPoint upstream source.sender.address.diversified ∧
      LegalPoint upstream source.sender.address.transmission.point := by
  obtain ⟨policy,_,derived,_,_,_⟩ := accepted_regulated upstream primitives agreement hash
    secret walletNk source key regulated accepted
  cases viewed : viewsAddress upstream primitives secret source.sender.address with
  | false =>
      simp only [ShielddNativeRegulatedLegality.deriveRegulated,viewed,Bool.false_eq_true,ite_false] at derived
      cases derived
  | true => exact viewed_address_legal upstream primitives secret source.sender.address viewed

/-- pari::compliance passes field(leaf.rnk_commitment), the canonical native
Fq reader of this same stored sender field. No caller-selected fieldValue is
left at the final registered gate. Source/codec instantiation remains global. -/
theorem registered_field_reader {Routes Origin Key Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (source : Source S Q Routes Origin Key) :
    ShielddNativeSdk.field (fq := fq) backend source.sender.registered =
      some (fq.integer source.sender.registered : F) :=
  ShielddNativeSdk.field_read backend source.sender.registered

def sourceSeed {Routes Origin Key : Type} (fq : GroupNativeSdk.FqBytes Q)
    (registeredColumn regulatedColumn : Nat) (source : Source S Q Routes Origin Key)
    (base : Nat → F) : Nat → F := fun column =>
  if column = regulatedColumn then (if source.regulated then 1 else 0)
  else if column = registeredColumn then (fq.integer source.sender.registered : F)
  else base column

theorem source_seed_registered {Routes Origin Key : Type}
    (registeredColumn regulatedColumn : Nat) (source : Source S Q Routes Origin Key)
    (base : Nat → F) (distinct : registeredColumn ≠ regulatedColumn) :
    sourceSeed fq registeredColumn regulatedColumn source base registeredColumn =
      (fq.integer source.sender.registered : F) := by
  simp only [sourceSeed,if_neg distinct,if_true]

theorem source_seed_regulated {Routes Origin Key : Type}
    (registeredColumn regulatedColumn : Nat) (source : Source S Q Routes Origin Key)
    (base : Nat → F) :
    sourceSeed fq registeredColumn regulatedColumn source base regulatedColumn =
      (if source.regulated then (1 : F) else 0) := by
  simp only [sourceSeed,if_true]

theorem source_seed_gate [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : Source S Q Routes Origin Key) (key : Q)
    (accepted : nullifierKey upstream primitives agreement hash secret walletNk source = some key)
    (registeredColumn regulatedColumn : Nat) (base : Nat → F)
    (distinct : registeredColumn ≠ regulatedColumn) :
    sourceSeed fq registeredColumn regulatedColumn source base regulatedColumn *
      ((fq.integer (hash 18 [key]) : F) -
        sourceSeed fq registeredColumn regulatedColumn source base registeredColumn) = 0 := by
  rw [source_seed_regulated,source_seed_registered registeredColumn regulatedColumn source base distinct]
  exact ShielddNativeRegisteredNullifier.registered_gate walletNk source.regulated source.policy
    (fun policy => ShielddNativeRegulatedLegality.deriveRegulated upstream primitives agreement hash
      secret source.sender.address source.asset policy.ring.ringKey source.sender.dhBase)
    (fun key => hash 18 [key]) source.sender.registered key
    (fun value => (fq.integer value : F)) accepted

theorem source_seed_preserves {Routes Origin Key : Type}
    (registeredColumn regulatedColumn : Nat) (source : Source S Q Routes Origin Key)
    (base : Nat → F) (column : Nat)
    (notRegistered : column ≠ registeredColumn) (notRegulated : column ≠ regulatedColumn) :
    sourceSeed fq registeredColumn regulatedColumn source base column = base column := by
  simp only [sourceSeed,if_neg notRegulated,if_neg notRegistered]

set_option pp.all true in
#check @callback_arguments
#print axioms callback_arguments
set_option pp.all true in
#check @accepted_regulated
#print axioms accepted_regulated
set_option pp.all true in
#check @accepted_views
#print axioms accepted_views
set_option pp.all true in
#check @registered_field_reader
#print axioms registered_field_reader
set_option pp.all true in
#check @source_seed_registered
#print axioms source_seed_registered
set_option pp.all true in
#check @source_seed_regulated
#print axioms source_seed_regulated
set_option pp.all true in
#check @source_seed_gate
#print axioms source_seed_gate
set_option pp.all true in
#check @source_seed_preserves
#print axioms source_seed_preserves

end ShielddSecurity.ShielddNativeActionWitnessAssociation
