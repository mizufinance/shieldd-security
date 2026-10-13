-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedDhInverse472
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def operandTerms (_index : Nat) : Linear := [(3763,1)]
def hintColumn (index : Nat) : Nat := 3765+index
def arithmeticStart (index : Nat) : Nat := 38038+2*index
def position (index : Nat) : Nat := 3771+index
def output (index : Nat) : Nat := 22738+arithmeticStart index

def rawRows : List Row := [⟨[(3763,52435875175126190479447740508185965837690552500527637822603658699938581184512),(3765,1)],[(60777,1)]⟩,⟨[(3763,1),(3765,1)],[(60776,4),(60777,1)]⟩]

def arithmeticRows (index : Nat) : List Row :=
  [rawRows.getD (2*index) ⟨[],[]⟩,rawRows.getD (2*index+1) ⟨[],[]⟩]
noncomputable def arithmeticCheck : Bool := (List.range 1).all (fun index => decide
  (CapturedFullArithmetic52.rowAt (arithmeticStart index)=(arithmeticRows index)[0]? ∧
   CapturedFullArithmetic52.rowAt (arithmeticStart index+1)=(arithmeticRows index)[1]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

noncomputable def productCheck : Bool := (List.range 1).all (fun index =>
  Compiler.checkRow p (arithmeticRows index)
    ⟨subtract [(hintColumn index,1)] (operandTerms index),[(output index+1,1)]⟩ &&
  Compiler.checkRow p (arithmeticRows index)
    ⟨[(hintColumn index,1)]++operandTerms index,[(output index+1,1)]++scaleLinear 4 [(output index,1)]⟩)
theorem product_checked : productCheck=true := by decide +kernel

def actualRow (index : Nat) : Row := ⟨[(output index,(p:Int)-1),(copy,1)],[]⟩
def actualRows : List Row := (List.range 1).map actualRow
def plainRows : List Row := actualRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
def normalizedRows : List Row := (List.range 1).map (fun index => ⟨[(0,1),(output index,-1)],[]⟩)
noncomputable def assertionCheck : Bool := (List.range 1).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+position index)=actualRows[index]?))
theorem assertion_checked : assertionCheck=true := by decide +kernel
noncomputable def reverseCheck : Bool := CompilerIndexed01.checkOriginalCoverage p 0
  plainRows.toArray normalizedRows.toArray (List.range 1).toArray
theorem reverse_checked : reverseCheck=true := by decide +kernel
noncomputable def soundCheck : Bool := (List.range 1).all (fun index =>
  Compiler.checkRow p plainRows ⟨subtract [(0,1)] [(output index,1)],[]⟩)
theorem sound_checked : soundCheck=true := by decide +kernel

variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (bound : index<1) : rho (output index)=eval rho (operandTerms index)*rho (hintColumn index) := by
  have positions := of_decide_eq_true (List.all_eq_true.mp arithmetic_checked index (List.mem_range.mpr bound))
  have lower : arithmeticStart index+1<177954 := by unfold arithmeticStart;omega
  have sat : Satisfies rho (arithmeticRows index) := by
    intro row member
    simp only [arithmeticRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact arithmetic (arithmeticStart index) (by omega) _ positions.1
    · exact arithmetic (arithmeticStart index+1) lower _ positions.2
  have checked := Bool.and_eq_true_iff.mp (List.all_eq_true.mp product_checked index (List.mem_range.mpr bound))
  have h := checked_product_sound rho (arithmeticRows index) [(hintColumn index,1)] (operandTerms index)
    [(output index,1)] [(output index+1,1)] four_ne_zero sat checked.1 checked.2
  have singleton (column : Nat) : eval rho [(column,1)]=rho column := by
    simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [singleton,singleton] at h
  exact h.trans (mul_comm _ _)

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+position index)) 1

theorem complete (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0) (values : ∀ index<1,rho (output index)=1) : Rows rho := by
  have normal : Satisfies rho normalizedRows := by
    intro row member
    obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
    have before : index<1 := List.mem_range.mp present
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

theorem sound (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (rows : Rows rho) (index : Nat) (bound : index<1) : eval rho (operandTerms index) ≠ 0 := by
  have actual : Satisfies rho actualRows := by
    intro row member
    obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp member
    have before : i<1 := by
      have h := (List.getElem?_eq_some_iff.mp found).1
      simpa only [actualRows,List.length_map,List.length_range] using h
    have position := of_decide_eq_true (List.all_eq_true.mp assertion_checked i (List.mem_range.mpr before))
    exact rows i before row (position.trans found)
  have plain : Satisfies rho plainRows := by
    intro row member
    change row ∈ actualRows.map (fun original => ⟨unoutline copy original.a,unoutline copy original.b⟩) at member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    change Square (eval rho (unoutline copy original.a)) (eval rho (unoutline copy original.b))
    rw [eval_unoutline rho copy original.a linked,eval_unoutline rho copy original.b linked]
    exact actual original originalMember
  have equality := checked_assertion_sound rho plainRows [(0,1)] [(output index,1)] plain
    (List.all_eq_true.mp sound_checked index (List.mem_range.mpr bound))
  have value : rho (output index)=1 := by simpa only [eval,Int.cast_one,one_mul,add_zero,zero] using equality.symm
  have product := products rho arithmetic index bound
  intro h
  rw [h,zero_mul] at product
  exact zero_ne_one (product.symm.trans value)
end ShielddSecurity.CapturedDhInverse472

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.operandTerms
#print axioms ShielddSecurity.CapturedDhInverse472.operandTerms

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.hintColumn
#print axioms ShielddSecurity.CapturedDhInverse472.hintColumn

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.arithmeticStart
#print axioms ShielddSecurity.CapturedDhInverse472.arithmeticStart

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.position
#print axioms ShielddSecurity.CapturedDhInverse472.position

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.output
#print axioms ShielddSecurity.CapturedDhInverse472.output

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.rawRows
#print axioms ShielddSecurity.CapturedDhInverse472.rawRows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.arithmeticRows
#print axioms ShielddSecurity.CapturedDhInverse472.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.arithmeticCheck
#print axioms ShielddSecurity.CapturedDhInverse472.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.arithmetic_checked
#print axioms ShielddSecurity.CapturedDhInverse472.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.productCheck
#print axioms ShielddSecurity.CapturedDhInverse472.productCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.product_checked
#print axioms ShielddSecurity.CapturedDhInverse472.product_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.actualRow
#print axioms ShielddSecurity.CapturedDhInverse472.actualRow

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.actualRows
#print axioms ShielddSecurity.CapturedDhInverse472.actualRows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.plainRows
#print axioms ShielddSecurity.CapturedDhInverse472.plainRows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.normalizedRows
#print axioms ShielddSecurity.CapturedDhInverse472.normalizedRows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.assertionCheck
#print axioms ShielddSecurity.CapturedDhInverse472.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.assertion_checked
#print axioms ShielddSecurity.CapturedDhInverse472.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.reverseCheck
#print axioms ShielddSecurity.CapturedDhInverse472.reverseCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.reverse_checked
#print axioms ShielddSecurity.CapturedDhInverse472.reverse_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.soundCheck
#print axioms ShielddSecurity.CapturedDhInverse472.soundCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.sound_checked
#print axioms ShielddSecurity.CapturedDhInverse472.sound_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.products
#print axioms ShielddSecurity.CapturedDhInverse472.products

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.Rows
#print axioms ShielddSecurity.CapturedDhInverse472.Rows

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.complete
#print axioms ShielddSecurity.CapturedDhInverse472.complete

set_option pp.all true in
#check @ShielddSecurity.CapturedDhInverse472.sound
#print axioms ShielddSecurity.CapturedDhInverse472.sound
