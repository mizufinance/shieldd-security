import ShielddSecurity.TierBase632
import ShielddSecurity.TierInitial634F00
import ShielddSecurity.TierInitial634F01
import ShielddSecurity.TierInitial634F02
import ShielddSecurity.TierInitial634F03
import ShielddSecurity.TierInitial634F04
import ShielddSecurity.AuthorizationPrefix462
import ShielddSecurity.VariableTraceBitIndex454
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierInitial635
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierLayout613 AuthorizationTraceSeed451
open TierFlagBindings630 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model
theorem precompute (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) :
    let rho := assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
    TransferOwnership.DoubleEquations (VariableWindowJoin443.point rho (TierBase632.baseX family) (TierBase632.baseY family))
      (VariableWindowColumns449.columnPoint rho (pointStart family)) ∧
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
      (VariableWindowColumns449.columnPoint rho (pointStart family))
      (VariableWindowJoin443.point rho (TierBase632.baseX family) (TierBase632.baseY family))
      (VariableWindowColumns449.columnPoint rho (pointStart family+2)) := by
  dsimp only
  have twice := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have triple := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family)=model.coordinates (2 • TierGroupDomain612.represented c w family legal) at twice
  change VariableWindowColumns449.columnPoint _ (pointStart family+2)=model.coordinates (3 • TierGroupDomain612.represented c w family legal) at triple
  rw [TierBase632.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial family,twice,triple]
  have nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F) := by
    rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square
  constructor
  · exact VariableGroupCompletion439.double_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _
  · have three : 2 • TierGroupDomain612.represented c w family legal+TierGroupDomain612.represented c w family legal=
        3 • TierGroupDomain612.represented c w family legal := by
      rw [show 3=2+1 from rfl,add_nsmul,one_nsmul]
    rw [←three]
    exact VariableGroupCompletion439.add_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _ _

theorem first_equation (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) :
    let rho := assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
    VariableWindowColumns449.columnPoint rho (pointStart family+4)=
      Group.windowPoint (rho (ScalarCanonicalRows395.bitStart (scalarFamily family)+250))
        (rho (ScalarCanonicalRows395.bitStart (scalarFamily family)+251))
        (VariableWindowJoin443.point rho (TierBase632.baseX family) (TierBase632.baseY family))
        (VariableWindowColumns449.columnPoint rho (pointStart family))
        (VariableWindowColumns449.columnPoint rho (pointStart family+2)) := by
  dsimp only
  have twice := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have triple := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := TierFlagBindings630.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 2 (by decide)
  change VariableWindowColumns449.columnPoint _ (pointStart family)=model.coordinates (2 • TierGroupDomain612.represented c w family legal) at twice
  change VariableWindowColumns449.columnPoint _ (pointStart family+2)=model.coordinates (3 • TierGroupDomain612.represented c w family legal) at triple
  change VariableWindowColumns449.columnPoint _ (pointStart family+4)=(windowAt (TierGroupDomain612.represented c w family legal) (scalar w family) 0).output at output
  have pair := VariableTraceBitIndex454.windows_bits model (TierGroupDomain612.represented c w family legal)
    (encodeBits 252 (scalar w family)) (by simp) empty 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (windowAt (TierGroupDomain612.represented c w family legal) (scalar w family) 0).low=(encodeBits 252 (scalar w family))[250]?.getD false at low
  change (windowAt (TierGroupDomain612.represented c w family legal) (scalar w family) 0).high=(encodeBits 252 (scalar w family))[251]?.getD false at high
  rw [output,TierBase632.coordinates original c w legal rkInitial authInitial initial senderInitial receiverInitial family,twice,triple,
    TierFlagBindings630.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 250 (by decide),
    TierFlagBindings630.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 251 (by decide),←low,←high]
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
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+11909+i)) 6 := by
  have one := TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (TierInitial634F00.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩)
  have initial := (TierInitial634F00.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩)
  exact append_six _ 11909 pre.1 pre.2 initial

theorem family1 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+12665+i)) 6 := by
  have one := TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (TierInitial634F01.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩)
  have initial := (TierInitial634F01.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩)
  exact append_six _ 12665 pre.1 pre.2 initial

theorem family2 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+13931+i)) 6 := by
  have one := TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (TierInitial634F02.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩)
  have initial := (TierInitial634F02.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩)
  exact append_six _ 13931 pre.1 pre.2 initial

theorem family3 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+15197+i)) 6 := by
  have one := TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (TierInitial634F03.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨3,by decide⟩)
  have initial := (TierInitial634F03.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨3,by decide⟩)
  exact append_six _ 15197 pre.1 pre.2 initial

theorem family4 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+16463+i)) 6 := by
  have one := TierFlagBindings630.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := TierFlagBindings630.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have pre := (TierInitial634F04.precompute_rows_iff _ one arithmetic).mpr (precompute original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨4,by decide⟩)
  have initial := (TierInitial634F04.initial_rows_iff _ one arithmetic).mpr (first_equation original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨4,by decide⟩)
  exact append_six _ 16463 pre.1 pre.2 initial

end ShielddSecurity.TierInitial635

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.precompute
#print axioms ShielddSecurity.TierInitial635.precompute

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.first_equation
#print axioms ShielddSecurity.TierInitial635.first_equation

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.append_six
#print axioms ShielddSecurity.TierInitial635.append_six

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.family0
#print axioms ShielddSecurity.TierInitial635.family0

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.family1
#print axioms ShielddSecurity.TierInitial635.family1

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.family2
#print axioms ShielddSecurity.TierInitial635.family2

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.family3
#print axioms ShielddSecurity.TierInitial635.family3

set_option pp.all true in
#check @ShielddSecurity.TierInitial635.family4
#print axioms ShielddSecurity.TierInitial635.family4
