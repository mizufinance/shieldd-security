import ShielddSecurity.PayloadInitial572F00
import ShielddSecurity.PayloadInitial572F01
import ShielddSecurity.AuthorizationPrefix462
import ShielddSecurity.VariableTraceBitIndex454
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadInitial573
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open PayloadFamilyLayout559 AuthorizationTraceSeed451
open PayloadBindings565 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model
theorem precompute (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) :
    let rho := assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
    TransferOwnership.DoubleEquations (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
      (VariableWindowColumns449.columnPoint rho (pointStart family)) ∧
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
      (VariableWindowColumns449.columnPoint rho (pointStart family))
      (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
      (VariableWindowColumns449.columnPoint rho (pointStart family+2)) := by
  dsimp only
  have twice := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have triple := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family)=model.coordinates (2 • PayloadGroupDomain557.represented c w legal) at twice
  change VariableWindowColumns449.columnPoint _ (pointStart family+2)=model.coordinates (3 • PayloadGroupDomain557.represented c w legal) at triple
  rw [PayloadBase568.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial,twice,triple]
  have nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F) := by
    rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square
  constructor
  · exact VariableGroupCompletion439.double_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _
  · have three : 2 • PayloadGroupDomain557.represented c w legal+PayloadGroupDomain557.represented c w legal=
        3 • PayloadGroupDomain557.represented c w legal := by
      rw [show 3=2+1 from rfl,add_nsmul,one_nsmul]
    rw [←three]
    exact VariableGroupCompletion439.add_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _ _

theorem first_equation (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) :
    let rho := assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
    VariableWindowColumns449.columnPoint rho (pointStart family+4)=
      Group.windowPoint (rho (ScalarCanonicalRows395.bitStart (scalarFamily family)+250))
        (rho (ScalarCanonicalRows395.bitStart (scalarFamily family)+251))
        (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
        (VariableWindowColumns449.columnPoint rho (pointStart family))
        (VariableWindowColumns449.columnPoint rho (pointStart family+2)) := by
  dsimp only
  have twice := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have triple := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := PayloadBindings565.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 2 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family)=model.coordinates (2 • PayloadGroupDomain557.represented c w legal) at twice
  change VariableWindowColumns449.columnPoint _ (pointStart family+2)=model.coordinates (3 • PayloadGroupDomain557.represented c w legal) at triple
  change VariableWindowColumns449.columnPoint _ (pointStart family+4)=(windowAt (PayloadGroupDomain557.represented c w legal) (scalar w family) 0).output at output
  have pair := VariableTraceBitIndex454.windows_bits model (PayloadGroupDomain557.represented c w legal)
    (encodeBits 252 (scalar w family)) (by simp) empty 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (windowAt (PayloadGroupDomain557.represented c w legal) (scalar w family) 0).low=(encodeBits 252 (scalar w family))[250]?.getD false at low
  change (windowAt (PayloadGroupDomain557.represented c w legal) (scalar w family) 0).high=(encodeBits 252 (scalar w family))[251]?.getD false at high
  rw [output,PayloadBase568.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial,twice,triple,
    PayloadBindings565.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 250 (by decide),
    PayloadBindings565.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 251 (by decide),←low,←high]
  exact AuthorizationPrefix462.first_output _ _

theorem append_six (rho : Nat → F) (start : Nat)
    (first : SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+start+i)) 2)
    (second : SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+(start+2)+i)) 2)
    (third : SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+(start+4)+i)) 2) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+start+i)) 6 := by
  intro i bound row found
  by_cases low : i<2
  · exact first i low row found
  · by_cases middle : i<4
    · apply second (i-2) (by omega) row
      simpa only [show 177954+(start+2)+(i-2)=177954+start+i by omega] using found
    · apply third (i-4) (by omega) row
      simpa only [show 177954+(start+4)+(i-4)=177954+start+i by omega] using found

theorem family0 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+5295+i)) 6 := by
  have one := PayloadBindings565.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := PayloadBindings565.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (PayloadInitial572F00.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩)
  have initial := (PayloadInitial572F00.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩)
  exact append_six _ 5295 pre.1 pre.2 initial

theorem family1 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+6698+i)) 6 := by
  have one := PayloadBindings565.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := PayloadBindings565.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (PayloadInitial572F01.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩)
  have initial := (PayloadInitial572F01.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩)
  exact append_six _ 6698 pre.1 pre.2 initial
end ShielddSecurity.PayloadInitial573
set_option pp.all true in
#check @ShielddSecurity.PayloadInitial573.precompute
#print axioms ShielddSecurity.PayloadInitial573.precompute
set_option pp.all true in
#check @ShielddSecurity.PayloadInitial573.first_equation
#print axioms ShielddSecurity.PayloadInitial573.first_equation
set_option pp.all true in
#check @ShielddSecurity.PayloadInitial573.append_six
#print axioms ShielddSecurity.PayloadInitial573.append_six
set_option pp.all true in
#check @ShielddSecurity.PayloadInitial573.family0
#print axioms ShielddSecurity.PayloadInitial573.family0
set_option pp.all true in
#check @ShielddSecurity.PayloadInitial573.family1
#print axioms ShielddSecurity.PayloadInitial573.family1
