import ShielddSecurity.BalanceBlindingBindings680
import ShielddSecurity.BalanceBlindingLocal676
import ShielddSecurity.BalanceBlindingJoin681
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingRows683
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceBlindingTrace675 (window trace empty)
open BalanceBlindingBindings680 (assignment)
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (layout : BalanceBlindingJoin681.Layout)
    (bitsColumn : layout.bits=22232)
    (pointColumn : layout.points=22484)
    (e : FixedWindowJoin488.Entry) (checked : BalanceBlindingJoin681.check layout e=true)
    (matched : BalanceBlindingMeaning674.check e=true) :
    VariableOperationAdapter434.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) e.operation := by
  have valid : BalanceBlindingJoin681.Valid layout e := of_decide_eq_true checked
  have lower : 1 ≤ e.index := valid.2.2.2.1
  have upper : e.index<126 := valid.2.2.2.2.1
  have pair := BalanceBlindingLocal676.bits w.blinding e.index upper
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window w.blinding e.index).low=(encodeBits 252 w.blinding)[2*e.index]?.getD false at low
  change (window w.blinding e.index).high=(encodeBits 252 w.blinding)[2*e.index+1]?.getD false at high
  have lowMeaning := BalanceBlindingBindings680.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial
    (2*e.index) (by omega)
  have highMeaning := BalanceBlindingBindings680.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial
    (2*e.index+1) (by omega)
  rw [←bitsColumn,←low] at lowMeaning
  have highColumn : layout.bits+(2*e.index+1)=layout.bits+2*e.index+1 := by omega
  rw [←bitsColumn,highColumn,←high] at highMeaning
  have previous := BalanceBlindingBindings680.point original c w legal rkInitial authInitial initial senderInitial receiverInitial
    (e.index-1) (by omega)
  rw [←pointColumn,←BalanceBlindingLocal676.before_positive w.blinding e.index lower] at previous
  exact BalanceBlindingJoin681.complete layout e checked matched
    (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceBlindingBindings680.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceBlindingBindings680.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (window w.blinding e.index).low (window w.blinding e.index).high
    (FixedTraceAccess486.before (model.coordinates 0) (trace w.blinding) empty e.index)
    (window w.blinding e.index).output lowMeaning highMeaning previous
    (by rw [pointColumn];exact BalanceBlindingBindings680.point original c w legal rkInitial authInitial initial senderInitial receiverInitial e.index upper)
    (BalanceBlindingLocal676.add_equations w.blinding e.index upper)
end ShielddSecurity.BalanceBlindingRows683
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingRows683.rows
#print axioms ShielddSecurity.BalanceBlindingRows683.rows
