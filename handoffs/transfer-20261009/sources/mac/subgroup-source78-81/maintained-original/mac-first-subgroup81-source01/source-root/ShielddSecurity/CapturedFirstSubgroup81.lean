import ShielddSecurity.CompilerSubgroupSource80
import ShielddSecurity.TransferFirstSubgroupCertificates01
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerArithmeticTransport41
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFirstSubgroup81
open Compiler
-- The aliases below name actual constants, not logical premises.
def d : Int := 19257038036680949359750312669786877991949435402254120286184196891950884077233
def negative : Int := (TransferFirstSubgroupData01.p : Int)-1
def shapeCheck : Bool :=
  (List.finRange 80).all (fun index => decide
    (TransferFirstSubgroupData01.graph.node index=CompilerSubgroupSource80.node d negative index)) &&
  decide (TransferFirstSubgroupData01.graph.assertions=CompilerSubgroupSource80.assertions)
theorem shape_checked : shapeCheck=true := by decide +kernel
theorem shape : CompilerSubgroupSource80.Matches TransferFirstSubgroupData01.graph d negative := by
  have checked:=Bool.and_eq_true_iff.mp shape_checked
  refine ⟨?_,of_decide_eq_true checked.2⟩
  intro index
  exact of_decide_eq_true (List.all_eq_true.mp checked.1 index (List.mem_finRange index))
def positions : List Nat := TransferFirstSubgroupData01.captureIndices.toList
def rows : List Row := TransferFirstSubgroupData01.originalRows.toList
def positionCheck : Bool := (List.range rows.length).all (fun index =>
  decide (positions[index]!<200770) &&
  decide (CapturedFullRelation58.rowAt positions[index]!=rows[index]?))
theorem positions_checked : positionCheck=true := by decide +kernel
variable {F : Type} [Field F]
theorem selected_rows (rho : Nat → F)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows := by
  intro row member
  obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
  have checked:=Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp positions_checked index (List.mem_range.mpr before))
  exact sat positions[index]! (of_decide_eq_true checked.1) row
    ((of_decide_eq_true checked.2).trans found)
variable [CharP F TransferFirstSubgroupData01.p]
theorem full_source (rho : Nat → F) (one : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Group.OnCurve (d:F) (⟨rho 16,rho 17⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (d:F) ⟨rho 16,rho 17⟩=⟨rho 14,rho 15⟩ := by
  have actual:=TransferFirstSubgroupCertificates01.arbitrary_assignment_sound rho one
    (CompilerArithmeticTransport41.four_ne_zero (F:=F)) (selected_rows rho sat)
  have result:=CompilerSubgroupSource80.graph_assertions_sound
    TransferFirstSubgroupData01.graph d negative
    (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input))
    (CompilerSubgroupSource80.modulus_negative_one (F:=F)) shape actual.2
  simpa only [CompilerSubgroupSource80.preimage,CompilerSubgroupSource80.point,
    TransferFirstSubgroupData01.inputTerms,eval,List.foldl_cons,List.foldl_nil,
    Int.cast_one,one_mul,zero_add] using result
end ShielddSecurity.CapturedFirstSubgroup81

set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.d
#print axioms ShielddSecurity.CapturedFirstSubgroup81.d
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.negative
#print axioms ShielddSecurity.CapturedFirstSubgroup81.negative
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.shapeCheck
#print axioms ShielddSecurity.CapturedFirstSubgroup81.shapeCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.shape_checked
#print axioms ShielddSecurity.CapturedFirstSubgroup81.shape_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.shape
#print axioms ShielddSecurity.CapturedFirstSubgroup81.shape
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.positions
#print axioms ShielddSecurity.CapturedFirstSubgroup81.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.rows
#print axioms ShielddSecurity.CapturedFirstSubgroup81.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.positionCheck
#print axioms ShielddSecurity.CapturedFirstSubgroup81.positionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.positions_checked
#print axioms ShielddSecurity.CapturedFirstSubgroup81.positions_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.selected_rows
#print axioms ShielddSecurity.CapturedFirstSubgroup81.selected_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstSubgroup81.full_source
#print axioms ShielddSecurity.CapturedFirstSubgroup81.full_source
