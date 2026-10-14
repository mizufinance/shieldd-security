import ShielddSecurity.PayloadBindings565
import ShielddSecurity.PayloadInputFrame566
import ShielddSecurity.PayloadSelector567
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadBase568
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] SemanticWordFrame373.assignment model

def baseX : Linear := [(87778,1),(copy,49822839976625491399435002605169580882773999909559575334089637637825427273330)]
def baseY : Linear := [(87780,1),(copy,29108985603249989484651727880329493522712908252517904247459350893053326313050)]

theorem selected (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (inputs : PayloadInputFrame566.Inputs rho w) :
    VariableWindowJoin443.point rho baseX baseY=SubgroupSeedCompletion203.fieldPoint (PayloadGroupDomain557.selected c w) := by
  have x := PayloadSelector567.x_value rho arithmetic
  have y := PayloadSelector567.y_value rho arithmetic
  change VariableWindowJoin443.point rho baseX baseY=SubgroupSeedCompletion203.fieldPoint
    (if w.regulated then w.registry.audit.payload else CapturedRegistryPointDomain75.sink)
  simp only [VariableWindowJoin443.point,baseX,baseY,eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,one,x,y,
    inputs.flag,inputs.payloadX,inputs.payloadY]
  cases flag : w.regulated <;>
    simp only [Bool.false_eq_true,if_false,if_true,SubgroupSeedCompletion203.fieldPoint,CapturedRegistryPointDomain75.sink]
  · apply congrArg₂ Group.Point.mk <;> ring
  · apply congrArg₂ Group.Point.mk <;> ring

theorem inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    PayloadInputFrame566.Inputs
      (PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact PayloadInputFrame566.rk (FixedFamilySeed549.seed (PayloadTraceSeed564.seed original c w legal) w)
    c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem coordinates (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowJoin443.point
      (PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) baseX baseY=
      model.coordinates (PayloadGroupDomain557.represented c w legal) := by
  rw [selected _ c w
    (PayloadBindings565.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (PayloadBindings565.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial)]
  exact (PayloadGroupDomain557.coordinates c w legal).symm
end ShielddSecurity.PayloadBase568

set_option pp.all true in
#check @ShielddSecurity.PayloadBase568.selected
#print axioms ShielddSecurity.PayloadBase568.selected

set_option pp.all true in
#check @ShielddSecurity.PayloadBase568.inputs
#print axioms ShielddSecurity.PayloadBase568.inputs

set_option pp.all true in
#check @ShielddSecurity.PayloadBase568.coordinates
#print axioms ShielddSecurity.PayloadBase568.coordinates
