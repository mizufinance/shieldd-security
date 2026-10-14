import ShielddSecurity.TierFlagBindings630
import ShielddSecurity.TierBase632
import ShielddSecurity.VariableFamilyLocal569
import ShielddSecurity.PayloadTraceLocal571
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierRows633
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierLayout613 VariableFamilyLayout562
open TierFlagBindings630 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5)
    (layout : Family) (baseX : layout.baseX=TierBase632.baseX family) (baseY : layout.baseY=TierBase632.baseY family)
    (pointColumn : layout.precomputeX=pointStart family)
    (bitsColumn : layout.bitsStart=ScalarCanonicalRows395.bitStart (scalarFamily family))
    (window : Nat) (e : VariableWindowJoin443.Entry) (checked : checkComplete ⟨layout,window,e⟩=true) :
    VariableWindowJoin443.Rows
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) e := by
  have complete : Complete ⟨layout,window,e⟩ := of_decide_eq_true checked
  have valid : Valid layout window e := of_decide_eq_true complete.1
  have lower := valid.1
  have upper := valid.2.1
  apply VariableFamilyLocal569.rows _ (TierGroupDomain612.represented c w family legal) (scalar w family) window layout e checked
    (TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
  · rw [baseX,baseY]
    exact TierBase632.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial family
  · rw [pointColumn]
    exact TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  · rw [pointColumn]
    exact TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  · have same : previous layout window=pointStart family+2*(3*window-1) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    exact (TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window-1) (by omega)).trans
      (PayloadTraceLocal571.previous _ (scalar w family) window lower)
  · have same : previous layout window+2=pointStart family+2*(3*window+0) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+0) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 0 lower (by decide))
    exact result
  · have same : previous layout window+4=pointStart family+2*(3*window+1) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+1) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 1 lower (by decide))
    exact result
  · have same : previous layout window+6=pointStart family+2*(3*window+2) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+2) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 2 lower (by decide))
    exact result
  · have same : layout.bitsStart+250-2*window=layout.bitsStart+(250-2*window) := by omega
    rw [same,bitsColumn]
    exact TierFlagBindings630.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family (250-2*window) (by omega)
  · have same : layout.bitsStart+251-2*window=layout.bitsStart+(251-2*window) := by omega
    rw [same,bitsColumn]
    exact TierFlagBindings630.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family (251-2*window) (by omega)
end ShielddSecurity.TierRows633
set_option pp.all true in
#check @ShielddSecurity.TierRows633.rows
#print axioms ShielddSecurity.TierRows633.rows
