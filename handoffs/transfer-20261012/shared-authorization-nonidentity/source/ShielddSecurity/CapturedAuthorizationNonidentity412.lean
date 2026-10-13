import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAuthorizationNonidentity412
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def pointColumn (index : Nat) : Nat := [1980].getD index 0
def arithmeticStart (index : Nat) : Nat := [27042].getD index 0
def position (index : Nat) : Nat := [1985].getD index 0
def output (index : Nat) : Nat := 22738+arithmeticStart index

def arithmeticRows (index : Nat) : List Row :=
  [⟨[(pointColumn index,(p:Int)-1),(pointColumn index+7,1)],[(output index+1,1)]⟩,
   ⟨[(pointColumn index,1),(pointColumn index+7,1)],[(output index,4),(output index+1,1)]⟩]
noncomputable def arithmeticCheck : Bool := (List.range 1).all (fun index => decide
  (CapturedFullArithmetic52.rowAt (arithmeticStart index)=(arithmeticRows index)[0]? ∧
   CapturedFullArithmetic52.rowAt (arithmeticStart index+1)=(arithmeticRows index)[1]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

noncomputable def productCheck : Bool := (List.range 1).all (fun index =>
  Compiler.checkRow p (arithmeticRows index)
    ⟨subtract [(pointColumn index+7,1)] [(pointColumn index,1)],[(output index+1,1)]⟩ &&
  Compiler.checkRow p (arithmeticRows index)
    ⟨[(pointColumn index+7,1)]++[(pointColumn index,1)],[(output index+1,1)]++scaleLinear 4 [(output index,1)]⟩)
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

variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (bound : index<1) : rho (output index)=rho (pointColumn index)*rho (pointColumn index+7) := by
  have positions := of_decide_eq_true (List.all_eq_true.mp arithmetic_checked index (List.mem_range.mpr bound))
  have lower : arithmeticStart index+1<177954 := by
    have same : index=0 := by omega
    subst index
    decide
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
    (rows : Rows rho) : rho 1980 ≠ 0 := by
  have actual : Satisfies rho actualRows := by
    intro row member
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    have bound : index<1 := by
      have before := (List.getElem?_eq_some_iff.mp found).1
      simpa only [actualRows,List.length_map,List.length_range] using before
    have position := of_decide_eq_true (List.all_eq_true.mp assertion_checked index (List.mem_range.mpr bound))
    exact rows index bound row (position.trans found)
  have plain : Satisfies rho plainRows := by
    intro row member
    change row ∈ actualRows.map (fun original => ⟨unoutline copy original.a,unoutline copy original.b⟩) at member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    change Square (eval rho (unoutline copy original.a)) (eval rho (unoutline copy original.b))
    rw [eval_unoutline rho copy original.a linked,eval_unoutline rho copy original.b linked]
    exact actual original originalMember
  have equality := checked_assertion_sound rho plainRows [(0,1)] [(output 0,1)] plain (by decide +kernel)
  have value : rho (output 0)=1 := by simpa only [eval,Int.cast_one,one_mul,add_zero,zero] using equality.symm
  have product := products rho arithmetic 0 (by decide)
  change rho (output 0)=rho 1980*rho 1987 at product
  intro h
  rw [h,zero_mul] at product
  exact zero_ne_one (product.symm.trans value)

end ShielddSecurity.CapturedAuthorizationNonidentity412

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.pointColumn
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.pointColumn

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticStart
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticStart

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.position
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.position

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.output
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.output

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticRows
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticCheck
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.arithmetic_checked
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.productCheck
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.productCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.product_checked
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.product_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.actualRow
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.actualRow

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.actualRows
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.actualRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.plainRows
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.plainRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.normalizedRows
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.normalizedRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.assertionCheck
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.assertion_checked
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.reverseCheck
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.reverseCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.reverse_checked
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.reverse_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.products
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.products

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.Rows
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.Rows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.complete
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.complete

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationNonidentity412.sound
#print axioms ShielddSecurity.CapturedAuthorizationNonidentity412.sound
