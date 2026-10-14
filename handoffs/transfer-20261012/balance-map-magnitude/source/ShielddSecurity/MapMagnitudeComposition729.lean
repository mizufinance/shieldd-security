import ShielddSecurity.MapMagnitudeJoin727
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapMagnitudeComposition729
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open MapAssignmentValues720 MapMagnitudeJoin727
attribute [local irreducible] MapAssignmentValues720.assignment model ConcreteCofactorModel01.model
  MapMagnitudeJoin727.BaseMeaning SatisfiesAt

theorem base_coordinates (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    BaseMeaning (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) u := by
  exact @MapMagnitudeJoin727.coordinates_from_values
    (MapAssignmentValues720.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) u
    (@MapAssignmentValues720.values original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (@MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeComposition729.base_coordinates
#print axioms ShielddSecurity.MapMagnitudeComposition729.base_coordinates

theorem magnitude_rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21914+i)) 390 := by
  have coordinates := base_coordinates original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  unfold BaseMeaning MapAssignmentValues720.assignment at coordinates
  unfold MapAssignmentValues720.assignment
  exact BalanceCombined696.magnitude_rows (BalanceMapSeed703.seed original u) c w legal (BalanceMapPoint701.represented u)
    rkInitial authInitial initial senderInitial receiverInitial
    coordinates

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeComposition729.magnitude_rows
#print axioms ShielddSecurity.MapMagnitudeComposition729.magnitude_rows

end ShielddSecurity.MapMagnitudeComposition729
