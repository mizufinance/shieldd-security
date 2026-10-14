import ShielddSecurity.DetectionGroupDomain611
import ShielddSecurity.TierBindings617
import ShielddSecurity.DetectionInputFrame625
import ShielddSecurity.DetectionSelector626
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionBase627
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] SemanticWordFrame373.assignment model

def baseX : Linear := [(33790,1),(copy,17832230285398775523840151435063191920633280288053987250961356462684628833490)]
def baseY : Linear := [(33792,1),(copy,52236742954115892447572473178524297982305297140137344394933767595493156073169)]

theorem selected (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (inputs : DetectionInputFrame625.Inputs rho w) :
    VariableWindowJoin443.point rho baseX baseY=SubgroupSeedCompletion203.fieldPoint (DetectionGroupDomain611.selected c w) := by
  have x := DetectionSelector626.x_value rho arithmetic
  have y := DetectionSelector626.y_value rho arithmetic
  change VariableWindowJoin443.point rho baseX baseY=SubgroupSeedCompletion203.fieldPoint
    (if w.regulated then w.registry.detection else DetectionGroupDomain611.defaultPoint)
  simp only [VariableWindowJoin443.point,baseX,baseY,eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,x,y,
    inputs.flag,inputs.detectionX,inputs.detectionY]
  cases flag : w.regulated <;>
    simp only [Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint,DetectionGroupDomain611.defaultPoint]
  · apply congrArg₂ Group.Point.mk <;> ring
  · apply congrArg₂ Group.Point.mk <;> ring

theorem inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    DetectionInputFrame625.Inputs
      (TierBindings617.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact DetectionInputFrame625.rk _ (DetectionGroupDomain611.baseCrypto c) w legal rkInitial authInitial initial senderInitial receiverInitial

theorem coordinates (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowJoin443.point
      (TierBindings617.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) baseX baseY=
      model.coordinates (DetectionGroupDomain611.represented c w legal) := by
  rw [selected _ c w
    (TierBindings617.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (TierBindings617.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial)]
  exact (DetectionGroupDomain611.coordinates c w legal).symm
end ShielddSecurity.DetectionBase627

set_option pp.all true in
#check @ShielddSecurity.DetectionBase627.selected
#print axioms ShielddSecurity.DetectionBase627.selected

set_option pp.all true in
#check @ShielddSecurity.DetectionBase627.inputs
#print axioms ShielddSecurity.DetectionBase627.inputs

set_option pp.all true in
#check @ShielddSecurity.DetectionBase627.coordinates
#print axioms ShielddSecurity.DetectionBase627.coordinates
