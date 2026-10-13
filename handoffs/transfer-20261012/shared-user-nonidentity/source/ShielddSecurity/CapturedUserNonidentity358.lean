import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedUserNonidentity358
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def pointColumn (index : Nat) : Nat := [1504,1512,1520,1742,1750,1758].getD index 0
def arithmeticStart (index : Nat) : Nat := [11134,11200,11266,19088,19154,19220].getD index 0
def position (index : Nat) : Nat := [1475,1482,1489,1730,1737,1744].getD index 0
def output (index : Nat) : Nat := 22738+arithmeticStart index

def arithmeticRows (index : Nat) : List Row :=
  [⟨[(pointColumn index,(p:Int)-1),(pointColumn index+7,1)],[(output index+1,1)]⟩,
   ⟨[(pointColumn index,1),(pointColumn index+7,1)],[(output index,4),(output index+1,1)]⟩]
noncomputable def arithmeticCheck : Bool := (List.range 6).all (fun index => decide
  (CapturedFullArithmetic52.rowAt (arithmeticStart index)=(arithmeticRows index)[0]? ∧
   CapturedFullArithmetic52.rowAt (arithmeticStart index+1)=(arithmeticRows index)[1]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

noncomputable def productCheck : Bool := (List.range 6).all (fun index =>
  Compiler.checkRow p (arithmeticRows index)
    ⟨subtract [(pointColumn index+7,1)] [(pointColumn index,1)],[(output index+1,1)]⟩ &&
  Compiler.checkRow p (arithmeticRows index)
    ⟨[(pointColumn index+7,1)]++[(pointColumn index,1)],[(output index+1,1)]++scaleLinear 4 [(output index,1)]⟩)
theorem product_checked : productCheck=true := by decide +kernel

def actualRow (index : Nat) : Row := ⟨[(output index,(p:Int)-1),(copy,1)],[]⟩
def actualRows : List Row := (List.range 6).map actualRow
def plainRows : List Row := actualRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
def normalizedRows : List Row := (List.range 6).map (fun index => ⟨[(0,1),(output index,-1)],[]⟩)
noncomputable def assertionCheck : Bool := (List.range 6).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+position index)=actualRows[index]?))
theorem assertion_checked : assertionCheck=true := by decide +kernel
noncomputable def reverseCheck : Bool := CompilerIndexed01.checkOriginalCoverage p 0
  plainRows.toArray normalizedRows.toArray (List.range 6).toArray
theorem reverse_checked : reverseCheck=true := by decide +kernel

variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (bound : index<6) : rho (output index)=rho (pointColumn index)*rho (pointColumn index+7) := by
  have positions := of_decide_eq_true (List.all_eq_true.mp arithmetic_checked index (List.mem_range.mpr bound))
  have lower : arithmeticStart index+1<177954 := by
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have sat : Satisfies rho (arithmeticRows index) := by
    intro row member
    simp only [arithmeticRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact arithmetic (arithmeticStart index) (by omega) _ positions.1
    · exact arithmetic (arithmeticStart index+1) lower _ positions.2
  have checked := Bool.and_eq_true_iff.mp (List.all_eq_true.mp product_checked index (List.mem_range.mpr bound))
  have h := checked_product_sound rho (arithmeticRows index) [(pointColumn index+7,1)] [(pointColumn index,1)]
    [(output index,1)] [(output index+1,1)] four_ne_zero sat checked.1 checked.2
  simpa only [eval,Int.cast_one,one_mul,add_zero,mul_comm] using h

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+position index)) 6

theorem complete (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0) (values : ∀ index<6,rho (output index)=1) : Rows rho := by
  have normal : Satisfies rho normalizedRows := by
    intro row member
    obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
    have before : index<6 := List.mem_range.mp present
    change Square (eval rho [(0,1),(output index,-1)]) (eval rho [])
    simp only [eval,zero,values index before,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,Square]
    ring
  have plain := transfer rho plainRows normalizedRows reverse_checked normal
  have actual : Satisfies rho actualRows := by
    intro row member
    have normalized := plain ⟨unoutline copy row.a,unoutline copy row.b⟩ (List.mem_map.mpr ⟨row,member,rfl⟩)
    change Square (eval rho (unoutline copy row.a)) (eval rho (unoutline copy row.b)) at normalized
    rw [eval_unoutline rho copy row.a linked,eval_unoutline rho copy row.b linked] at normalized
    exact normalized
  intro index bound row found
  have position := of_decide_eq_true (List.all_eq_true.mp assertion_checked index (List.mem_range.mpr bound))
  exact actual row (List.mem_iff_getElem?.mpr ⟨index,position.symm.trans found⟩)
end ShielddSecurity.CapturedUserNonidentity358

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.pointColumn
#print axioms ShielddSecurity.CapturedUserNonidentity358.pointColumn

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.arithmeticStart
#print axioms ShielddSecurity.CapturedUserNonidentity358.arithmeticStart

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.position
#print axioms ShielddSecurity.CapturedUserNonidentity358.position

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.output
#print axioms ShielddSecurity.CapturedUserNonidentity358.output

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.arithmeticRows
#print axioms ShielddSecurity.CapturedUserNonidentity358.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.arithmeticCheck
#print axioms ShielddSecurity.CapturedUserNonidentity358.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.arithmetic_checked
#print axioms ShielddSecurity.CapturedUserNonidentity358.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.productCheck
#print axioms ShielddSecurity.CapturedUserNonidentity358.productCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.product_checked
#print axioms ShielddSecurity.CapturedUserNonidentity358.product_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.actualRow
#print axioms ShielddSecurity.CapturedUserNonidentity358.actualRow

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.actualRows
#print axioms ShielddSecurity.CapturedUserNonidentity358.actualRows

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.plainRows
#print axioms ShielddSecurity.CapturedUserNonidentity358.plainRows

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.normalizedRows
#print axioms ShielddSecurity.CapturedUserNonidentity358.normalizedRows

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.assertionCheck
#print axioms ShielddSecurity.CapturedUserNonidentity358.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.assertion_checked
#print axioms ShielddSecurity.CapturedUserNonidentity358.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.reverseCheck
#print axioms ShielddSecurity.CapturedUserNonidentity358.reverseCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.reverse_checked
#print axioms ShielddSecurity.CapturedUserNonidentity358.reverse_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.products
#print axioms ShielddSecurity.CapturedUserNonidentity358.products

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.Rows
#print axioms ShielddSecurity.CapturedUserNonidentity358.Rows

set_option pp.all true in
#check @ShielddSecurity.CapturedUserNonidentity358.complete
#print axioms ShielddSecurity.CapturedUserNonidentity358.complete
