import ShielddSecurity.MapAssetHash739
import ShielddSecurity.MapInverseRows722
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashMeaning740
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment model SatisfiesAt PoseidonNatural192.hash Poseidon.hash3

theorem base_asset (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 6=(w.asset:F) := by
  unfold AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact SharedRegulatedValue316.asset_meaning _ _ w initial

set_option pp.all true in
#check @ShielddSecurity.MapAssetHashMeaning740.base_asset
#print axioms ShielddSecurity.MapAssetHashMeaning740.base_asset

theorem asset (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 6=(w.asset:F) := by
  unfold assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment
    OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment
    PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact base_asset _ _ w legal rkInitial authInitial initial senderInitial receiverInitial

set_option pp.all true in
#check @ShielddSecurity.MapAssetHashMeaning740.asset
#print axioms ShielddSecurity.MapAssetHashMeaning740.asset

noncomputable def input (c : Crypto) (w : TransferSem.Witness) : F :=
  ((BalanceBlindingDomain670.crypto c).hash .assetGenerator [w.asset]:F)

theorem natural_hash (c : Crypto) (w : TransferSem.Witness) :
    input c w=Poseidon.hash3 (Poseidon.castParameters MapAssetHash739.parameters) 26 [(w.asset:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide representation
    .assetGenerator [w.asset]:F)=_
  rw [show Poseidon.castParameters MapAssetHash739.parameters=(RegistryNatural193.small : Poseidon.Parameters F 3) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_pos (by change 1 ≤ 2;decide)]
  rfl

set_option pp.all true in
#check @ShielddSecurity.MapAssetHashMeaning740.natural_hash
#print axioms ShielddSecurity.MapAssetHashMeaning740.natural_hash

theorem hash_input : MapFirstCubic707.hashInput=MapAssetHash739.result := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.MapAssetHashMeaning740.hash_input
#print axioms ShielddSecurity.MapAssetHashMeaning740.hash_input

theorem meaning (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      MapFirstCubic707.hashInput=input c w := by
  have zero := MapInverseRows722.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := MapAssignmentValues720.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have hash := MapAssetHash739.hash _ zero (copied.trans zero.symm) arithmetic
  rw [asset original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at hash
  rw [hash_input]
  exact hash.trans (natural_hash c w).symm

set_option pp.all true in
#check @ShielddSecurity.MapAssetHashMeaning740.meaning
#print axioms ShielddSecurity.MapAssetHashMeaning740.meaning
end ShielddSecurity.MapAssetHashMeaning740
