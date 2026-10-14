import ShielddSecurity.MapAssetHashMeaning740
import ShielddSecurity.SubgroupNonidentity350
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetDomain743
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model ConcreteCofactorModel01.model

noncomputable def hashValue (asset : Nat) : F :=
  Poseidon.hash3 (Poseidon.castParameters MapAssetHash739.parameters) 26 [(asset:F)]
noncomputable def assetPoint (asset : Nat) : TransferCore.Affine :=
  RegistryPointSemantic200.encode representation (BalanceMapPoint701.eight (hashValue asset))
noncomputable def withAsset (c : Crypto) : Crypto := {c with assetGenerator:=assetPoint}
noncomputable def crypto (c : Crypto) : Crypto := BalanceBlindingDomain670.crypto (withAsset c)

theorem hash_input (c : Crypto) (w : TransferSem.Witness) :
    MapAssetHashMeaning740.input (withAsset c) w=hashValue w.asset :=
  MapAssetHashMeaning740.natural_hash (withAsset c) w

theorem coordinates (asset : Nat) : SubgroupSeedCompletion203.fieldPoint (assetPoint asset)=
    BalanceMapPoint701.eight (hashValue asset) :=
  ConcreteAuthorizationCrypto430.decode_encode _

theorem member (asset : Nat) : CapturedSubgroupModel199.Member ConcreteCofactorModel01.model
    (BalanceMapPoint701.eight (hashValue asset)) :=
  ⟨BalanceMapPoint701.represented (hashValue asset),BalanceMapPoint701.represented_coordinates (hashValue asset),
    BalanceMapPoint701.represented_subgroup (hashValue asset)⟩

theorem encoded_identity : RegistryPointSemantic200.encode representation (Group.identityPoint : Group.Point F)=
    (⟨0,1⟩ : TransferCore.Affine) := by
  simp only [RegistryPointSemantic200.encode,representation,Group.identityPoint,ZMod.val_zero,ZMod.val_one]

theorem legal_nonidentity (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    BalanceMapPoint701.eight (hashValue w.asset)≠Group.identityPoint := by
  obtain ⟨_,_,_,_,_,_,_,_,_,balance⟩ := legal.2.1
  have nonidentity : TransferSem.nonidentity (assetPoint w.asset) := balance.2
  intro equal
  apply nonidentity
  exact (congrArg (RegistryPointSemantic200.encode representation) equal).trans encoded_identity

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    (BalanceMapPoint701.eight (MapAssetHashMeaning740.input (withAsset c) w)).x≠0 := by
  rw [hash_input]
  exact SubgroupNonidentity350.member_x_nonzero ConcreteCofactorModel01.model _
    (member w.asset) (legal_nonidentity c w legal)
end ShielddSecurity.MapAssetDomain743

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.hash_input
#print axioms ShielddSecurity.MapAssetDomain743.hash_input

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.coordinates
#print axioms ShielddSecurity.MapAssetDomain743.coordinates

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.member
#print axioms ShielddSecurity.MapAssetDomain743.member

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.encoded_identity
#print axioms ShielddSecurity.MapAssetDomain743.encoded_identity

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.legal_nonidentity
#print axioms ShielddSecurity.MapAssetDomain743.legal_nonidentity

set_option pp.all true in
#check @ShielddSecurity.MapAssetDomain743.x_nonzero
#print axioms ShielddSecurity.MapAssetDomain743.x_nonzero
