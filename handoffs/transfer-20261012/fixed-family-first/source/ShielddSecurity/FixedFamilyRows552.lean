import ShielddSecurity.FixedFamilyBindings551
import ShielddSecurity.AuthorizationFixedLocal493
import ShielddSecurity.FixedFamilyJoin543
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyRows552
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (window trace empty)
open FixedFamilyBindings551 (assignment)
open FixedFamilyLayout545
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (family : Fin 8) (layout : FixedFamilyJoin543.Layout)
    (bitsColumn : layout.bits=ScalarCanonicalRows395.bitStart (scalarFamily family))
    (pointColumn : layout.points=pointStart family)
    (e : FixedWindowJoin488.Entry) (checked : FixedFamilyJoin543.check layout e=true)
    (matched : FixedWindowMeaning491.check e=true) :
    VariableOperationAdapter434.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) e.operation := by
  have valid : FixedFamilyJoin543.Valid layout e := of_decide_eq_true checked
  have lower : 1 ≤ e.index := valid.2.2.2.1
  have upper : e.index<126 := valid.2.2.2.2.1
  have pair := AuthorizationFixedLocal493.bits (scalar w family) e.index upper
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) e.index).low=(encodeBits 252 (scalar w family))[2*e.index]?.getD false at low
  change (window (scalar w family) e.index).high=(encodeBits 252 (scalar w family))[2*e.index+1]?.getD false at high
  have lowMeaning := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family
    (2*e.index) (by omega)
  have highMeaning := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family
    (2*e.index+1) (by omega)
  rw [←bitsColumn,←low] at lowMeaning
  have highColumn : layout.bits+(2*e.index+1)=layout.bits+2*e.index+1 := by omega
  rw [←bitsColumn,highColumn,←high] at highMeaning
  have previous := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family
    (e.index-1) (by omega)
  rw [←pointColumn,←AuthorizationFixedLocal493.before_positive (scalar w family) e.index lower] at previous
  exact FixedFamilyJoin543.complete layout e checked matched
    (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (window (scalar w family) e.index).low (window (scalar w family) e.index).high
    (FixedTraceAccess486.before (model.coordinates 0) (trace (scalar w family)) empty e.index)
    (window (scalar w family) e.index).output lowMeaning highMeaning previous
    (by rw [pointColumn];exact FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family e.index upper)
    (AuthorizationFixedLocal493.add_equations (scalar w family) e.index upper)
end ShielddSecurity.FixedFamilyRows552
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyRows552.rows
#print axioms ShielddSecurity.FixedFamilyRows552.rows
