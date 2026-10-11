import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGap145
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def arithmeticRows : List Row := @ROWS@
def left (index : Nat) : Linear := @LEFT@
def right (index : Nat) : Linear := @RIGHT@
def output (index : Nat) : Nat := @OUTPUT@
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
