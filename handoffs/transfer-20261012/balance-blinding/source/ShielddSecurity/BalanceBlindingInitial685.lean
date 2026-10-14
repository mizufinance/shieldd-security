import ShielddSecurity.BalanceBlindingBindings680
import ShielddSecurity.AuthorizationFixedInitial499
import ShielddSecurity.BalanceBlindingInitial684F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingInitial685
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceBlindingBindings680 (assignment)
open BalanceBlindingTrace675 (window)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model
theorem first_output (scalar : Nat) :
    (window scalar 0).output=Group.windowPoint
      (if (window scalar 0).low then 1 else 0) (if (window scalar 0).high then 1 else 0)
      (FixedSelectorAdapter480.base (BalanceBlindingTables673.table 0).1)
      (FixedSelectorAdapter480.twice (BalanceBlindingTables673.table 0).1)
      (FixedSelectorAdapter480.triple (BalanceBlindingTables673.table 0).1) := by
  have equations := BalanceBlindingLocal676.add_equations scalar 0 (by decide)
  simp only [FixedTraceAccess486.before,model.identity] at equations
  exact AuthorizationFixedInitial499.identity_add _ _ _ equations

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+22559+i)) 2 := by
  apply (BalanceBlindingInitial684F00.rows_iff _
    (BalanceBlindingBindings680.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceBlindingBindings680.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  have pair := BalanceBlindingLocal676.bits w.blinding 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window w.blinding 0).low=(encodeBits 252 w.blinding)[0]?.getD false at low
  change (window w.blinding 0).high=(encodeBits 252 w.blinding)[1]?.getD false at high
  have lowBit := BalanceBlindingBindings680.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial 0 (by decide)
  have highBit := BalanceBlindingBindings680.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial 1 (by decide)
  have output := BalanceBlindingBindings680.point original c w legal rkInitial authInitial initial senderInitial receiverInitial 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 22484=(window w.blinding 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 22232=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 22233=_ at highBit
  rw [output,lowBit,highBit,←low,←high,BalanceBlindingInitial684F00.table_points.1,
    BalanceBlindingInitial684F00.table_points.2.1,BalanceBlindingInitial684F00.table_points.2.2]
  exact first_output w.blinding
set_option pp.all true in
#check @all_rows
#print axioms all_rows
set_option pp.all true in
#check @first_output
#print axioms first_output
end ShielddSecurity.BalanceBlindingInitial685
