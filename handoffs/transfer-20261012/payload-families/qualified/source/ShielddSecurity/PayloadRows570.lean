import ShielddSecurity.PayloadBase568
import ShielddSecurity.VariableFamilyLocal569
import ShielddSecurity.PayloadTraceLocal571
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadRows570
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open PayloadFamilyLayout559 VariableFamilyLayout562
open PayloadBindings565 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2)
    (layout : Family) (baseX : layout.baseX=PayloadBase568.baseX) (baseY : layout.baseY=PayloadBase568.baseY)
    (pointColumn : layout.precomputeX=pointStart family)
    (bitsColumn : layout.bitsStart=ScalarCanonicalRows395.bitStart (scalarFamily family))
    (window : Nat) (e : VariableWindowJoin443.Entry) (checked : checkComplete ⟨layout,window,e⟩=true) :
    VariableWindowJoin443.Rows
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) e := by
  have complete : Complete ⟨layout,window,e⟩ := of_decide_eq_true checked
  have valid : Valid layout window e := of_decide_eq_true complete.1
  have lower := valid.1
  have upper := valid.2.1
  apply VariableFamilyLocal569.rows _ (PayloadGroupDomain557.represented c w legal) (scalar w family) window layout e checked
    (PayloadBindings565.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (PayloadBindings565.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
  · rw [baseX,baseY]
    exact PayloadBase568.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · rw [pointColumn]
    exact PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  · rw [pointColumn]
    exact PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  · have same : previous layout window=pointStart family+2*(3*window-1) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    exact (PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window-1) (by omega)).trans
      (PayloadTraceLocal571.previous _ (scalar w family) window lower)
  · have same : previous layout window+2=pointStart family+2*(3*window+0) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+0) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 0 lower (by decide))
    exact result
  · have same : previous layout window+4=pointStart family+2*(3*window+1) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+1) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 1 lower (by decide))
    exact result
  · have same : previous layout window+6=pointStart family+2*(3*window+2) := by
      unfold previous
      rw [pointColumn]
      omega
    rw [same]
    have result := (PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (3*window+2) (by omega)).trans
      (PayloadTraceLocal571.component _ (scalar w family) window 2 lower (by decide))
    exact result
  · have same : layout.bitsStart+250-2*window=layout.bitsStart+(250-2*window) := by omega
    rw [same,bitsColumn]
    exact PayloadBindings565.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family (250-2*window) (by omega)
  · have same : layout.bitsStart+251-2*window=layout.bitsStart+(251-2*window) := by omega
    rw [same,bitsColumn]
    exact PayloadBindings565.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family (251-2*window) (by omega)
end ShielddSecurity.PayloadRows570
set_option pp.all true in
#check @ShielddSecurity.PayloadRows570.rows
#print axioms ShielddSecurity.PayloadRows570.rows
