import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGap145
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def arithmeticRows : List Row := [⟨[(1110,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1112,1)],[(33775,1)]⟩,⟨[(1110,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1112,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(33774,4),(33775,1)]⟩,⟨[(981,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1110,1),(1112,1),(33774,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(33777,1)]⟩,⟨[(981,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1110,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1112,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33774,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,3)],[(33776,4),(33777,1)]⟩,⟨[(1371,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1373,1)],[(33783,1)]⟩,⟨[(1371,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1373,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(33782,4),(33783,1)]⟩,⟨[(1242,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1371,1),(1373,1),(33782,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(33785,1)]⟩,⟨[(1242,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1371,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1373,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33782,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,3)],[(33784,4),(33785,1)]⟩,⟨[(33776,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33784,1)],[(33787,1)]⟩,⟨[(33776,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33784,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(33786,4),(33787,1)]⟩,⟨[(10,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33786,1)],[(33789,1)]⟩,⟨[(10,52435875175126190479447740508185965837690552500527637822603658699938581184512),(33786,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(33788,4),(33789,1)]⟩]
def left (index : Nat) : Linear := match index with
  | 0 => [(0,1),(1110,-1)]
  | 1 => [(0,1),(981,-1)]
  | 2 => [(0,1),(1371,-1)]
  | 3 => [(0,1),(1242,-1)]
  | 4 => [(0,1),(33776,-1)]
  | 5 => [(0,1),(10,-1)]
  | _ => []
def right (index : Nat) : Linear := match index with
  | 0 => [(0,1),(1112,-1)]
  | 1 => [(0,2),(1110,-1),(1112,-1),(33774,-1)]
  | 2 => [(0,1),(1373,-1)]
  | 3 => [(0,2),(1371,-1),(1373,-1),(33782,-1)]
  | 4 => [(0,1),(33784,-1)]
  | 5 => [(0,1),(33786,-1)]
  | _ => []
def output (index : Nat) : Nat := match index with
  | 0 => 33774
  | 1 => 33776
  | 2 => 33782
  | 3 => 33784
  | 4 => 33786
  | 5 => 33788
  | _ => 0
def auxiliary (index : Nat) : Nat := output index+1
noncomputable def sourceAt (index : Nat) : Option Row :=
  CapturedArithmetic45B0048.block.actual (if index<4 then 444+index else 448+index)
noncomputable def rowCheck : Bool := decide (arithmeticRows.length=12) &&
  (List.range 12).all (fun index => decide (sourceAt index=arithmeticRows[index]?))
theorem row_checked : rowCheck=true := by decide +kernel
noncomputable def normalizedRows : List Row := arithmeticRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
noncomputable def pairCheck (index : Nat) : Bool :=
  Compiler.checkRow p normalizedRows ⟨subtract (left index) (right index),[(auxiliary index,1)]⟩ &&
  Compiler.checkRow p normalizedRows ⟨left index++right index,[(auxiliary index,1)]++scaleLinear 4 [(output index,1)]⟩
noncomputable def productionCheck : Bool := (List.range 6).all pairCheck
theorem production_checked : productionCheck=true := by decide +kernel
theorem arithmetic_position (index : Nat) (bound : index<12) :
    CapturedFullArithmetic52.rowAt (if index<4 then 11036+index else 11040+index)=arithmeticRows[index]? := by
  have localRow:=of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp row_checked).2 index (List.mem_range.mpr bound))
  have root : CapturedFullArithmetic52.rowAt (if index<4 then 11036+index else 11040+index)=sourceAt index := by
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 ∨ index=10 ∨ index=11 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  exact root.trans localRow
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
theorem normalization_sound (rho : Nat → F) (sat : Satisfies rho arithmeticRows)
    (linked : rho copy=rho 0) : Satisfies rho normalizedRows := by
  intro row member
  obtain ⟨original,present,rfl⟩:=List.mem_map.mp member
  change Square (eval rho (unoutline copy original.a)) (eval rho (unoutline copy original.b))
  rw [eval_unoutline rho copy original.a linked,eval_unoutline rho copy original.b linked]
  exact sat original present
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho copy=rho 0) (index : Nat) (bound : index<6) : rho (output index)=eval rho (left index)*eval rho (right index) := by
  have sat : Satisfies rho arithmeticRows := by
    intro row member
    obtain ⟨i,found⟩:=List.mem_iff_getElem?.mp member
    obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
    have lower : i<12 := by
      have count : arithmeticRows.length=12 := of_decide_eq_true (Bool.and_eq_true_iff.mp row_checked).1
      rw [count] at before
      exact before
    exact arithmetic (if i<4 then 11036+i else 11040+i) (by split <;> omega) row
      ((arithmetic_position i lower).trans found)
  have normalized:=normalization_sound rho sat linked
  have checked:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp production_checked index (List.mem_range.mpr bound))
  have h:=checked_product_sound rho normalizedRows (left index) (right index) [(output index,1)] [(auxiliary index,1)]
    four_ne_zero normalized checked.1 checked.2
  simpa only [eval,Int.cast_one,one_mul,add_zero] using h
theorem gap_polynomial (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (one : rho 0=1) (linked : rho copy=rho 0) :
    rho 33788=(1-rho 10)*(1-(1-(1-rho 981)*(1-rho 1110*rho 1112))*
      (1-(1-rho 1242)*(1-rho 1371*rho 1373))) := by
  have a:=products rho arithmetic linked 0 (by decide)
  have b:=products rho arithmetic linked 1 (by decide)
  have c:=products rho arithmetic linked 2 (by decide)
  have d:=products rho arithmetic linked 3 (by decide)
  have e:=products rho arithmetic linked 4 (by decide)
  have f:=products rho arithmetic linked 5 (by decide)
  simp [left,right,output,eval,one] at a b c d e f
  rw [f,e,d,c,b,a]
  ring
end ShielddSecurity.CapturedRegistryGap145

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.arithmeticRows
#print axioms ShielddSecurity.CapturedRegistryGap145.arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.left
#print axioms ShielddSecurity.CapturedRegistryGap145.left
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.right
#print axioms ShielddSecurity.CapturedRegistryGap145.right
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.output
#print axioms ShielddSecurity.CapturedRegistryGap145.output
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.auxiliary
#print axioms ShielddSecurity.CapturedRegistryGap145.auxiliary
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.sourceAt
#print axioms ShielddSecurity.CapturedRegistryGap145.sourceAt
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.rowCheck
#print axioms ShielddSecurity.CapturedRegistryGap145.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.row_checked
#print axioms ShielddSecurity.CapturedRegistryGap145.row_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.normalizedRows
#print axioms ShielddSecurity.CapturedRegistryGap145.normalizedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.pairCheck
#print axioms ShielddSecurity.CapturedRegistryGap145.pairCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.productionCheck
#print axioms ShielddSecurity.CapturedRegistryGap145.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.production_checked
#print axioms ShielddSecurity.CapturedRegistryGap145.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.arithmetic_position
#print axioms ShielddSecurity.CapturedRegistryGap145.arithmetic_position
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.normalization_sound
#print axioms ShielddSecurity.CapturedRegistryGap145.normalization_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.products
#print axioms ShielddSecurity.CapturedRegistryGap145.products
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGap145.gap_polynomial
#print axioms ShielddSecurity.CapturedRegistryGap145.gap_polynomial
