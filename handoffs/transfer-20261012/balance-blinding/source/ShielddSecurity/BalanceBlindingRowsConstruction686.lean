import ShielddSecurity.BalanceBlindingRows683
import ShielddSecurity.BalanceBlindingInitial685
import ShielddSecurity.BalanceBlindingCapture682F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingRowsConstruction686
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceBlindingBindings680 (assignment)
attribute [local irreducible] assignment BalanceBlindingCapture682F00.entries

noncomputable def RegularRows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22561+i)) 250

theorem entry (index : Nat) (lower : 1 ≤ index) (upper : index<126) :
    ∃ e∈BalanceBlindingCapture682F00.entries,e.index=index := by
  have member : index∈BalanceBlindingCapture682F00.entries.map (fun e => e.index) := by
    rw [BalanceBlindingCapture682F00.schedule]
    exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
  exact List.mem_map.mp member

theorem regular_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    RegularRows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro offset before row found
  obtain ⟨e,member,index⟩ := entry (offset/2+1) (by omega) (by omega)
  have checked := List.all_eq_true.mp BalanceBlindingCapture682F00.checked e member
  have matched := List.all_eq_true.mp BalanceBlindingCapture682F00.matched e member
  have rows := BalanceBlindingRows683.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial BalanceBlindingCapture682F00.layout rfl rfl e checked matched
  have valid : BalanceBlindingJoin681.Valid BalanceBlindingCapture682F00.layout e := of_decide_eq_true checked
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,position⟩
  apply rows (offset%2) (by omega) row
  change CapturedFullRelation58.rowAt (177954+e.operation.assertionStart+offset%2)=some row
  change e.operation.assertionStart=22561+2*(e.index-1) at position
  have same : 177954+e.operation.assertionStart+offset%2=177954+22561+offset := by omega
  rw [same]
  exact found

noncomputable def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22559+i)) 252

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro offset before row found
  by_cases first : offset<2
  · exact BalanceBlindingInitial685.all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial offset first row found
  · apply regular_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial (offset-2) (by omega) row
    change CapturedFullRelation58.rowAt (177954+22561+(offset-2))=some row
    simpa only [show 177954+22561+(offset-2)=177954+22559+offset by omega] using found
end ShielddSecurity.BalanceBlindingRowsConstruction686

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingRowsConstruction686.entry
#print axioms ShielddSecurity.BalanceBlindingRowsConstruction686.entry

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingRowsConstruction686.regular_rows
#print axioms ShielddSecurity.BalanceBlindingRowsConstruction686.regular_rows

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingRowsConstruction686.all_rows
#print axioms ShielddSecurity.BalanceBlindingRowsConstruction686.all_rows
