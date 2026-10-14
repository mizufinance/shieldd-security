import ShielddSecurity.TierFlagInputFacts667
import ShielddSecurity.TierFlagSeedFacts665
import ShielddSecurity.TierFlagRetained629
import ShielddSecurity.TierFlagMeaning619
import ShielddSecurity.DetectionBase627
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagBindings630
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierFlagLayout620 (columns flags)

theorem seed_boolean (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈flags) :
    TierFlagSeed623.seed original w column=0 ∨ TierFlagSeed623.seed original w column=1 := by
  exact TierFlagSeedFacts665.seed_boolean original w column member

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.seed_boolean
#print axioms ShielddSecurity.TierFlagBindings630.seed_boolean

noncomputable def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  TierBindings617.assignment (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem flag_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (member : column∈columns) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=TierFlagSeed623.seed original w column := by
  unfold assignment
  exact TierFlagRetained629.tier_frame (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial column member (seed_boolean original w column)

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.flag_frame
#print axioms ShielddSecurity.TierFlagBindings630.flag_frame

theorem address_bounds (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index : Fin 4) :
    TierFlagSeed623.left w index<TransferCore.fieldModulus ∧
    TierFlagSeed623.right w index<TransferCore.fieldModulus := by
  exact TierFlagSeedFacts665.address_bounds (DetectionGroupDomain611.crypto c) w legal index

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.address_bounds
#print axioms ShielddSecurity.TierFlagBindings630.address_bounds

theorem inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    TierFlagMeaning619.Inputs (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  have header := DetectionBase627.inputs (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
  have regulated : assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 10=
      if w.regulated then 1 else 0 := by
    unfold assignment
    exact header.flag
  exact TierFlagInputFacts667.inputs original (DetectionGroupDomain611.crypto c) w legal
    (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) regulated
    (flag_frame original c w legal rkInitial authInitial initial senderInitial receiverInitial)

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.inputs
#print axioms ShielddSecurity.TierFlagBindings630.inputs

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact TierBindings617.arithmetic (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.arithmetic
#print axioms ShielddSecurity.TierFlagBindings630.arithmetic

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment
  exact TierBindings617.copied (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.copied
#print axioms ShielddSecurity.TierFlagBindings630.copied

theorem flagged_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 108486=if flagged w then 1 else 0 := by
  have volume := legal.2.1.2.2.2.2.2.2.1
  exact TierFlagMeaning619.value _ w (arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (copied original c w legal rkInitial authInitial initial senderInitial receiverInitial) (inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial) volume.2.2.2.2.1

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.flagged_value
#print axioms ShielddSecurity.TierFlagBindings630.flagged_value

open ConcreteJubjubField01 TransferSem TierLayout613
open AuthorizationTraceSeed451 (hintPoint)
theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) (index : Nat) (before : index<378) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (TierLayout613.pointStart family+2*index)=hintPoint (TierGroupDomain612.represented c w family legal) (TierLayout613.scalar w family) index := by
  unfold assignment
  exact TierBindings617.point (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial family index before

set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.point
#print axioms ShielddSecurity.TierFlagBindings630.point

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) (index : Nat) (bound : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
      (ScalarCanonicalRows395.bitStart (TierLayout613.scalarFamily family)+index)=
      if (encodeBits 252 (TierLayout613.scalar w family))[index]?.getD false then 1 else 0 := by
  unfold assignment
  exact TierBindings617.bits (TierFlagSeed623.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial family index bound


set_option pp.all true in
#check @ShielddSecurity.TierFlagBindings630.bits
#print axioms ShielddSecurity.TierFlagBindings630.bits

end ShielddSecurity.TierFlagBindings630
