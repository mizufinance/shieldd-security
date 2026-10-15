import ShielddSecurity.PublicStatementInputs995
import ShielddSecurity.VolumePathValues947
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementMeaning996
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model VolumePathAssignment942.assignment
  SatisfiesAt PoseidonNatural192.hash Poseidon.hash6

theorem natural (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .transferStatement
      (TransferSem.publicFields (BalanceBlindingDomain670.crypto c) w):F)=
    Poseidon.hash6 (Poseidon.castParameters PublicStatementHash977C187.parameters) 34
      ((TransferSem.publicFields (BalanceBlindingDomain670.crypto c) w).map fun n : Nat => (n:F)) := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide
    ConcreteRegistrySharedEncoding294.representation .transferStatement
    (TransferSem.publicFields (BalanceBlindingDomain670.crypto c) w):F)=_
  rw [show Poseidon.castParameters PublicStatementHash977C187.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by simpa only [List.length_map,TransferSem.public_fields_length] using (show ¬64≤2 by decide))]
  rfl

variable (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem hash :
    let rho := VolumePathAssignment942.assignment (PublicStatementSeed980.seed original w)
      (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
    eval rho PublicStatementHash977C187.result=
      ((MapAssetDomain743.crypto c).hash .transferStatement (TransferSem.publicFields (MapAssetDomain743.crypto c) w):F) := by
  have zero := VolumePathValues947.zero (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := VolumePathValues947.copied (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := VolumePathValues947.arithmetic (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := PublicStatementHash977C187.hash _ zero (copied.trans zero.symm) arithmetic
  rw [PublicStatementInputs995.inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural (MapAssetDomain743.withAsset c) w).symm

theorem claimed :
    let rho := VolumePathAssignment942.assignment (PublicStatementSeed980.seed original w)
      (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
    eval rho PublicStatementHash977C187.result=rho 22737 :=
  (hash original c w legal rkInitial authInitial initial senderInitial receiverInitial).trans
    (PublicStatementHeader994.claim_field (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
      (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial).symm
end ShielddSecurity.PublicStatementMeaning996

set_option pp.all true in
#check @ShielddSecurity.PublicStatementMeaning996.natural
#print axioms ShielddSecurity.PublicStatementMeaning996.natural

set_option pp.all true in
#check @ShielddSecurity.PublicStatementMeaning996.hash
#print axioms ShielddSecurity.PublicStatementMeaning996.hash

set_option pp.all true in
#check @ShielddSecurity.PublicStatementMeaning996.claimed
#print axioms ShielddSecurity.PublicStatementMeaning996.claimed
