import ShielddSecurity.AuthorizationFixedBindings492
import ShielddSecurity.AuthorizationFixedLocal493
import ShielddSecurity.FixedWindowCompletion494
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedWindows496
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (assignment window trace empty)
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (e : FixedWindowJoin488.Entry) (checked : FixedWindowJoin488.check e=true)
    (matched : FixedWindowMeaning491.check e=true) :
    VariableOperationAdapter434.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) e.operation := by
  have valid : FixedWindowJoin488.Valid e := of_decide_eq_true checked
  have lower : 1 ≤ e.index := valid.2.2.2.1
  have upper : e.index<126 := valid.2.2.2.2.1
  have pair := AuthorizationFixedLocal493.bits w.auth.randomizer e.index upper
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window w.auth.randomizer e.index).low=(encodeBits 252 w.auth.randomizer)[2*e.index]?.getD false at low
  change (window w.auth.randomizer e.index).high=(encodeBits 252 w.auth.randomizer)[2*e.index+1]?.getD false at high
  have lowMeaning := AuthorizationFixedBindings492.bits original c w legal authInitial initial senderInitial receiverInitial
    (2*e.index) (by omega)
  have highMeaning := AuthorizationFixedBindings492.bits original c w legal authInitial initial senderInitial receiverInitial
    (2*e.index+1) (by omega)
  rw [←low] at lowMeaning
  have highColumn : 3767+(2*e.index+1)=3768+2*e.index := by omega
  rw [highColumn,←high] at highMeaning
  have previous := AuthorizationFixedBindings492.point original c w legal authInitial initial senderInitial receiverInitial
    (e.index-1) (by omega)
  have previousColumn : 4019+2*(e.index-1)=4017+2*e.index := by omega
  rw [previousColumn,←AuthorizationFixedLocal493.before_positive w.auth.randomizer e.index lower] at previous
  exact FixedWindowCompletion494.complete e checked matched
    (assignment original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationFixedBindings492.copied original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationFixedBindings492.arithmetic original c w legal authInitial initial senderInitial receiverInitial)
    (window w.auth.randomizer e.index).low (window w.auth.randomizer e.index).high
    (FixedTraceAccess486.before (model.coordinates 0) (trace w.auth.randomizer) empty e.index)
    (window w.auth.randomizer e.index).output lowMeaning highMeaning previous
    (AuthorizationFixedBindings492.point original c w legal authInitial initial senderInitial receiverInitial e.index upper)
    (AuthorizationFixedLocal493.add_equations w.auth.randomizer e.index upper)
end ShielddSecurity.AuthorizationFixedWindows496
set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedWindows496.rows
#print axioms ShielddSecurity.AuthorizationFixedWindows496.rows
