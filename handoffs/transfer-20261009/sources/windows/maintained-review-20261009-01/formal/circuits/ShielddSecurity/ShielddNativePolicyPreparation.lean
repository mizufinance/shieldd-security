import ShielddSecurity.ShielddNativePolicyDecoder
import ShielddSecurity.ShielddNativeActionWitnessAssociation

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativePolicyPreparation

open TransferNativeRegulatedSource ShielddNativeRegulatedLegality ShielddNativeAddressLegality

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- storage::get_asset_policy uses the selected asset's original stored bytes;
local_compliance requires Some policy only for its regulated branch, and
action_witness copies that policy under the same first-spend asset key. The
arguments are the corresponding independent storage/proof/user query results.
This function checks no path, current root, user status or asset nonzero law.
Those complete API checks are not replaced by this field-constructor view. -/
noncomputable def prepare {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeTail : List GroupByteCodec.Byte → Option (ShielddNativePolicyDecoder.Tail Routes Origin Key))
    (asset : Q) (regulated : Bool) (assetLeaf : Leaf Q S (AuditKeys S))
    (sender : ShielddNativeActionWitnessAssociation.Sender S Q)
    (stored : Option (List GroupByteCodec.Byte)) :
    Option (ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) :=
  if regulated then do
    let raw ← stored
    let policy ← ShielddNativePolicyDecoder.fromBytes upstream authorityCheck decodeTail raw
    pure ⟨asset,regulated,assetLeaf,sender,some policy⟩
  else some ⟨asset,regulated,assetLeaf,sender,none⟩

/-- This is exactly ActionWitness::validate's policy branch, after its asset
path/value checks and before its user checks. It retains the complete selected
leaf and policy projection used in IndexedLeaf::from_policy. -/
noncomputable def validatePolicy {Routes Origin Key : Type}
    (hashes : Hashes Q S Routes Origin)
    (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) :
    Option (ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) :=
  match source.policy,source.regulated with
  | some policy,true => match checkPolicy hashes source.assetLeaf policy with
    | none => none
    | some _ => some source
  | none,false => some source
  | _,_ => none

theorem prepared_regulated {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeTail : List GroupByteCodec.Byte → Option (ShielddNativePolicyDecoder.Tail Routes Origin Key))
    (asset : Q) (assetLeaf : Leaf Q S (AuditKeys S))
    (sender : ShielddNativeActionWitnessAssociation.Sender S Q)
    (stored : Option (List GroupByteCodec.Byte))
    (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key)
    (accepted : prepare upstream authorityCheck decodeTail asset true assetLeaf sender stored = some source) :
    ∃ raw policy, stored = some raw ∧
      ShielddNativePolicyDecoder.fromBytes upstream authorityCheck decodeTail raw = some policy ∧
      source = ⟨asset,true,assetLeaf,sender,some policy⟩ := by
  cases storedRead : stored with
  | none => simp [prepare,storedRead] at accepted
  | some raw =>
    cases policyRead : ShielddNativePolicyDecoder.fromBytes upstream authorityCheck decodeTail raw with
    | none => simp [prepare,storedRead,policyRead] at accepted
    | some policy =>
      have same : (⟨asset,true,assetLeaf,sender,some policy⟩ :
          ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) = source :=
        Option.some.inj (by simpa [prepare,storedRead,policyRead] using accepted)
      exact ⟨raw,policy,rfl,policyRead,same.symm⟩

theorem validated_preparation_legal {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeTail : List GroupByteCodec.Byte → Option (ShielddNativePolicyDecoder.Tail Routes Origin Key))
    (hashes : Hashes Q S Routes Origin) (asset : Q) (assetLeaf : Leaf Q S (AuditKeys S))
    (sender : ShielddNativeActionWitnessAssociation.Sender S Q)
    (stored : Option (List GroupByteCodec.Byte))
    (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key)
    (prepared : prepare upstream authorityCheck decodeTail asset true assetLeaf sender stored = some source)
    (validated : validatePolicy hashes source = some source) :
    ∃ raw policy, stored = some raw ∧ source.policy = some policy ∧
      ShielddNativePolicyDecoder.fromBytes upstream authorityCheck decodeTail raw = some policy ∧
      checkPolicy hashes source.assetLeaf policy = some policy ∧
      LegalPoint upstream source.assetLeaf.params.issuer ∧ LegalPoint upstream source.assetLeaf.ring.ringKey := by
  obtain ⟨raw,policy,storedRead,decoded,same⟩ := prepared_regulated upstream authorityCheck decodeTail
    asset assetLeaf sender stored source prepared
  subst source
  cases checked : checkPolicy hashes assetLeaf policy with
  | none => simp only [validatePolicy,checked] at validated; cases validated
  | some output =>
    obtain ⟨identity,_,_,_⟩ := checked_policy_fields hashes assetLeaf policy output checked
    subst output
    have legal := ShielddNativePolicyDecoder.checked_leaf_keys upstream authorityCheck decodeTail
      raw policy hashes assetLeaf decoded checked
    exact ⟨raw,policy,storedRead,rfl,decoded,checked,legal.2.2.2⟩

set_option pp.all true in
#check @prepared_regulated
#print axioms prepared_regulated
set_option pp.all true in
#check @validated_preparation_legal
#print axioms validated_preparation_legal

end ShielddSecurity.ShielddNativePolicyPreparation
