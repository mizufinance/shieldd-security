import ShielddSecurity.VolumePathAssignment942
import ShielddSecurity.BalanceSemanticJoin757
import ShielddSecurity.BalanceFinalConstruction754
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementBalance981
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
  VolumePathAssignment942.assignment VolumeHashAssignment892.assignment
  RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment
  RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
  MapAssignmentValues720.assignment
  VolumePathSeed936.seed VolumeHashSeed886.seed RoutingParameterSeed866.seed
  VolumeCandidateSeed848.seed VolumeBoundarySeed836.seed RoutingPrecisionSeed811.seed
  SemanticCopiesSeed798.seed CheckingInverseSeed783.seed RecoveryInverseSeed778.seed
  OutputAmountDomain767.seed DetectionNonidentityDomain759.seed

variable (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem point :
    let rho := VolumePathAssignment942.assignment original (BalanceFinalConstruction754.input c w)
      (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
    Group.Point.mk (rho 195230) (rho 195234)=
      SubgroupSeedCompletion203.fieldPoint (TransferSem.balance (MapAssetDomain743.crypto c) w) := by
  dsimp only
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment
    RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
    VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment
    RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment
  exact BalanceSemanticJoin757.point _ c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem public_coordinates :
    let rho := VolumePathAssignment942.assignment original (BalanceFinalConstruction754.input c w)
      (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
    rho 195230=(((TransferSem.publicFields (MapAssetDomain743.crypto c) w)[7]?.getD 0:Nat):F) ∧
    rho 195234=(((TransferSem.publicFields (MapAssetDomain743.crypto c) w)[8]?.getD 0:Nat):F) := by
  have equality := point original c w legal rkInitial authInitial initial senderInitial receiverInitial
  dsimp only
  rw [BalanceSemanticJoin757.public_x,BalanceSemanticJoin757.public_y]
  exact ⟨congrArg Group.Point.x equality,congrArg Group.Point.y equality⟩
end ShielddSecurity.PublicStatementBalance981

set_option pp.all true in
#check @ShielddSecurity.PublicStatementBalance981.point
#print axioms ShielddSecurity.PublicStatementBalance981.point

set_option pp.all true in
#check @ShielddSecurity.PublicStatementBalance981.public_coordinates
#print axioms ShielddSecurity.PublicStatementBalance981.public_coordinates
