import ShielddSecurity.BalanceSignedGroup755
import ShielddSecurity.BalanceFinalDomain751
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSemantic756
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model ConcreteCofactorModel01.model

def signed (w : TransferSem.Witness) : Int :=
  (((w.spends 0).amount+(w.spends 1).amount:Nat):Int)-(((w.outputs 0).amount+(w.outputs 1).amount:Nat):Int)
def scalar (w : TransferSem.Witness) : Nat := (signed w % (TransferCore.scalarOrder:Int)).toNat

theorem scalar_bound (w : TransferSem.Witness) : scalar w<2^255 := by
  have nonnegative := Int.emod_nonneg (signed w) (show (TransferCore.scalarOrder:Int)≠0 by decide)
  have before := Int.emod_lt_of_pos (signed w) (show 0<(TransferCore.scalarOrder:Int) by decide)
  have bound : scalar w<TransferCore.scalarOrder := by unfold scalar;omega
  exact lt_trans bound (by decide)

theorem signed_magnitude (w : TransferSem.Witness) :
    signed w=if BalanceSignBindings652.negative w then -(RemainingWordSeed369.magnitude w:Int)
      else (RemainingWordSeed369.magnitude w:Int) := by
  unfold signed BalanceSignBindings652.negative RemainingWordSeed369.magnitude
  dsimp only
  split <;> split <;> simp_all only [decide_eq_true_eq,decide_eq_false_iff_not] <;> omega

theorem signed_coordinates (u : F) (w : TransferSem.Witness) :
    model.coordinates (scalar w • BalanceMapPoint701.represented u)=BalanceFinalDomain751.left u w := by
  have killed : TransferCore.scalarOrder • BalanceMapPoint701.represented u=0 :=
    BalanceMapPoint701.represented_subgroup u
  rw [scalar,BalanceSignedGroup755.reduced_scalar _ _ (by decide) killed,signed_magnitude]
  unfold BalanceFinalDomain751.left
  split
  · rw [neg_smul,natCast_zsmul,BalanceSignedGroup755.coordinates_neg
      (CapturedFirstSubgroup81.d:F) imaginary model
      (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square]
    rfl
  · rw [natCast_zsmul]
    rfl

theorem asset_multiply (c : Crypto) (w : TransferSem.Witness) :
    SubgroupSeedCompletion203.fieldPoint ((MapAssetDomain743.crypto c).mul (scalar w)
      ((MapAssetDomain743.crypto c).assetGenerator w.asset))=
      BalanceFinalDomain751.left (MapAssetDomain743.hashValue w.asset) w := by
  let chosen := AuthorizationFixedDomain485.withGenerator
    (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding (MapAssetDomain743.withAsset c)))
  have coordinates : model.coordinates (BalanceMapPoint701.represented (MapAssetDomain743.hashValue w.asset))=
      BalanceMapPoint701.eight (MapAssetDomain743.hashValue w.asset) :=
    (MapAssignmentValues720.model_coordinates _).trans (BalanceMapPoint701.represented_coordinates _)
  have encoded : MapAssetDomain743.assetPoint w.asset=
      RegistryPointSemantic200.encode representation
        (model.coordinates (BalanceMapPoint701.represented (MapAssetDomain743.hashValue w.asset))) := by
    unfold MapAssetDomain743.assetPoint
    rw [coordinates]
  change SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto chosen).mul (scalar w)
    (MapAssetDomain743.assetPoint w.asset))=_
  rw [encoded]
  exact (ConcreteAuthorizationCrypto430.multiply_coordinates chosen _ (scalar w) (scalar_bound w)).trans
    (signed_coordinates (MapAssetDomain743.hashValue w.asset) w)

theorem balance_coordinates (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    SubgroupSeedCompletion203.fieldPoint (TransferSem.balance (MapAssetDomain743.crypto c) w)=
      Group.affineAdd (CapturedFirstSubgroup81.d:F)
        (BalanceFinalDomain751.left (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w) w)
        (BalanceFinalDomain751.right w) := by
  change SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation
    (Group.affineAdd (CapturedFirstSubgroup81.d:F)
      (SubgroupSeedCompletion203.fieldPoint ((MapAssetDomain743.crypto c).mul (scalar w)
        ((MapAssetDomain743.crypto c).assetGenerator w.asset)))
      (SubgroupSeedCompletion203.fieldPoint ((MapAssetDomain743.crypto c).mul w.blinding
        ((MapAssetDomain743.crypto c).blindingGenerator)))))=_
  have blinding := BalanceBlindingDomain670.multiply_coordinates (MapAssetDomain743.withAsset c) w.blinding
    (lt_trans (BalanceBlindingBindings680.scalar_bound (MapAssetDomain743.withAsset c) w legal) (by decide))
  change SubgroupSeedCompletion203.fieldPoint ((MapAssetDomain743.crypto c).mul w.blinding
    ((MapAssetDomain743.crypto c).blindingGenerator))=BalanceFinalDomain751.right w at blinding
  rw [ConcreteAuthorizationCrypto430.decode_encode,asset_multiply,blinding,MapAssetDomain743.hash_input]
end ShielddSecurity.BalanceSemantic756

set_option pp.all true in
#check @ShielddSecurity.BalanceSemantic756.scalar_bound
#print axioms ShielddSecurity.BalanceSemantic756.scalar_bound

set_option pp.all true in
#check @ShielddSecurity.BalanceSemantic756.signed_magnitude
#print axioms ShielddSecurity.BalanceSemantic756.signed_magnitude

set_option pp.all true in
#check @ShielddSecurity.BalanceSemantic756.signed_coordinates
#print axioms ShielddSecurity.BalanceSemantic756.signed_coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceSemantic756.asset_multiply
#print axioms ShielddSecurity.BalanceSemantic756.asset_multiply

set_option pp.all true in
#check @ShielddSecurity.BalanceSemantic756.balance_coordinates
#print axioms ShielddSecurity.BalanceSemantic756.balance_coordinates
