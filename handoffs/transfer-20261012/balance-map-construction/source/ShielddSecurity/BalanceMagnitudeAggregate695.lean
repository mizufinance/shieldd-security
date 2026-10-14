import ShielddSecurity.BalanceBoundRows664
import ShielddSecurity.BalanceBoundInitial668
import ShielddSecurity.BalanceMagnitudeCapture644F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceMagnitudeAggregate695
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceMagnitudeLayout641
open BalanceMagnitudeCapture644F00 (layout entries)
open BalanceMagnitudeBindings663 (assignment)
attribute [local irreducible] assignment model entries

-- The captured asset-base correspondence is an explicit, undischarged premise.
theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (base : curve.Point)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (baseMeaning : VariableWindowJoin443.point
      (assignment original c w legal base rkInitial authInitial initial senderInitial receiverInitial)
      [(190237,1)] [(190241,1)]=model.coordinates base) :
    SatisfiesAt (assignment original c w legal base rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21914+i)) 390 := by
  intro offset before row found
  by_cases first : offset<6
  · exact BalanceBoundInitial668.rows original c w legal base rkInitial authInitial initial
      senderInitial receiverInitial baseMeaning offset first row found
  · have member : (offset-6)/6+1∈entries.map Prod.fst := by
      rw [BalanceMagnitudeCapture644F00.schedule]
      exact List.mem_range'.mpr ⟨(offset-6)/6,by omega,by omega⟩
    obtain ⟨entry,member,index⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp BalanceMagnitudeCapture644F00.checked entry member
    have complete : Complete ⟨layout,entry.1,entry.2⟩ := of_decide_eq_true checked
    have valid : Valid layout entry.1 entry.2 := of_decide_eq_true complete.1
    rcases valid with ⟨_,_,firstPosition,secondPosition,addPosition,_⟩
    have rows := BalanceBoundRows664.rows original c w legal base rkInitial authInitial initial
      senderInitial receiverInitial layout rfl rfl baseMeaning entry.1 entry.2 checked
    change entry.2.first.assertionStart=21914+6+6*(entry.1-1) at firstPosition
    change entry.2.second.assertionStart=21914+8+6*(entry.1-1) at secondPosition
    change entry.2.addition.assertionStart=21914+10+6*(entry.1-1) at addPosition
    by_cases low : (offset-6)%6<2
    · apply rows.1 ((offset-6)%6) low row
      change CapturedFullRelation58.rowAt (177954+entry.2.first.assertionStart+(offset-6)%6)=some row
      simpa only [show 177954+entry.2.first.assertionStart+(offset-6)%6=177954+21914+offset by omega] using found
    · by_cases middle : (offset-6)%6<4
      · apply rows.2.1 ((offset-6)%6-2) (by omega) row
        change CapturedFullRelation58.rowAt (177954+entry.2.second.assertionStart+((offset-6)%6-2))=some row
        simpa only [show 177954+entry.2.second.assertionStart+((offset-6)%6-2)=177954+21914+offset by omega] using found
      · apply rows.2.2 ((offset-6)%6-4) (by omega) row
        change CapturedFullRelation58.rowAt (177954+entry.2.addition.assertionStart+((offset-6)%6-4))=some row
        simpa only [show 177954+entry.2.addition.assertionStart+((offset-6)%6-4)=177954+21914+offset by omega] using found
end ShielddSecurity.BalanceMagnitudeAggregate695
set_option pp.all true in
#check @ShielddSecurity.BalanceMagnitudeAggregate695.all_rows
#print axioms ShielddSecurity.BalanceMagnitudeAggregate695.all_rows
