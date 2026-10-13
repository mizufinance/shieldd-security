import ShielddSecurity.AuthorizationFixedInitialCapture498
import ShielddSecurity.AuthorizationFixedConstruction497
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedInitial499
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (assignment window)
attribute [local irreducible] assignment

theorem identity_add {F : Type} [Field F] (d : F) (right output : Group.Point F)
    (equations : TransferOwnership.AddEquations d Group.identityPoint right output) : output=right := by
  have coordinates : output.x=right.x ∧ output.y=right.y := by
    simpa only [TransferOwnership.AddEquations,Group.identityPoint,Group.delta,
      mul_zero,zero_mul,mul_one,one_mul,zero_add,add_zero,sub_zero,add_sub_cancel_right] using equations
  cases output
  cases right
  exact congrArg₂ Group.Point.mk coordinates.1 coordinates.2

theorem first_output (scalar : Nat) :
    (window scalar 0).output=Group.windowPoint
      (if (window scalar 0).low then 1 else 0) (if (window scalar 0).high then 1 else 0)
      (FixedSelectorAdapter480.base (AuthorizationFixedTables490.table 0).1)
      (FixedSelectorAdapter480.twice (AuthorizationFixedTables490.table 0).1)
      (FixedSelectorAdapter480.triple (AuthorizationFixedTables490.table 0).1) := by
  have equations := AuthorizationFixedLocal493.add_equations scalar 0 (by decide)
  simp only [FixedTraceAccess486.before,model.identity] at equations
  exact identity_add _ _ _ equations

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+4028+i)) 2 := by
  apply (AuthorizationFixedInitialCapture498.rows_iff _
    (AuthorizationFixedBindings492.copied original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationFixedBindings492.arithmetic original c w legal authInitial initial senderInitial receiverInitial)).mpr
  have pair := AuthorizationFixedLocal493.bits w.auth.randomizer 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window w.auth.randomizer 0).low=(encodeBits 252 w.auth.randomizer)[0]?.getD false at low
  change (window w.auth.randomizer 0).high=(encodeBits 252 w.auth.randomizer)[1]?.getD false at high
  have lowBit := AuthorizationFixedBindings492.bits original c w legal authInitial initial senderInitial receiverInitial 0 (by decide)
  have highBit := AuthorizationFixedBindings492.bits original c w legal authInitial initial senderInitial receiverInitial 1 (by decide)
  have output := AuthorizationFixedBindings492.point original c w legal authInitial initial senderInitial receiverInitial 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 4019=(window w.auth.randomizer 0).output at output
  change assignment original c w legal authInitial initial senderInitial receiverInitial 3767=_ at lowBit
  change assignment original c w legal authInitial initial senderInitial receiverInitial 3768=_ at highBit
  rw [output,lowBit,highBit,←low,←high]
  exact first_output w.auth.randomizer

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      AuthorizationFixedBindings492.Earlier original c w legal authInitial initial senderInitial receiverInitial ∧
      AuthorizationFixedConstruction497.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial)
        (fun i => CapturedFullRelation58.rowAt (177954+4028+i)) 2 := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    AuthorizationFixedConstruction497.legal_completed original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,rows,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationFixedInitial499

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitial499.identity_add
#print axioms ShielddSecurity.AuthorizationFixedInitial499.identity_add

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitial499.first_output
#print axioms ShielddSecurity.AuthorizationFixedInitial499.first_output

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitial499.all_rows
#print axioms ShielddSecurity.AuthorizationFixedInitial499.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedInitial499.legal_completed
#print axioms ShielddSecurity.AuthorizationFixedInitial499.legal_completed
