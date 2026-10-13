-- GENERATED from rows.json by generate.py. Do not hand edit.
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedAuthorizationShared419
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def operandTerms (index : Nat) : Linear :=
  [[(1504,1)],[(1512,1)],[(1520,1)],[(copy,49822839976625491399435002605169580882773999909559575334089637637825427273330),(33796,1)],[(6,1)]].getD index []
def hintColumn (index : Nat) : Nat := 1988+index
def arithmeticStart (index : Nat) : Nat := 27044+2*index
def position (index : Nat) : Nat := 1986+index
def output (index : Nat) : Nat := 22738+arithmeticStart index

def rawRows : List Row := [⟨[(1504,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1988,1)],[(49783,1)]⟩,⟨[(1504,1),(1988,1)],[(49782,4),(49783,1)]⟩,⟨[(1512,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1989,1)],[(49785,1)]⟩,⟨[(1512,1),(1989,1)],[(49784,4),(49785,1)]⟩,⟨[(1520,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1990,1)],[(49787,1)]⟩,⟨[(1520,1),(1990,1)],[(49786,4),(49787,1)]⟩,⟨[(1991,1),(33796,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(49789,1)]⟩,⟨[(1991,1),(33796,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(49788,4),(49789,1)]⟩,⟨[(6,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1992,1)],[(49791,1)]⟩,⟨[(6,1),(1992,1)],[(49790,4),(49791,1)]⟩]

def arithmeticRows (index : Nat) : List Row :=
  [rawRows.getD (2*index) ⟨[],[]⟩,rawRows.getD (2*index+1) ⟨[],[]⟩]
noncomputable def arithmeticCheck : Bool := (List.range 5).all (fun index => decide
  (CapturedFullArithmetic52.rowAt (arithmeticStart index)=(arithmeticRows index)[0]? ∧
   CapturedFullArithmetic52.rowAt (arithmeticStart index+1)=(arithmeticRows index)[1]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

noncomputable def productCheck : Bool := (List.range 5).all (fun index =>
  Compiler.checkRow p (arithmeticRows index)
    ⟨subtract [(hintColumn index,1)] (operandTerms index),[(output index+1,1)]⟩ &&
  Compiler.checkRow p (arithmeticRows index)
    ⟨[(hintColumn index,1)]++operandTerms index,[(output index+1,1)]++scaleLinear 4 [(output index,1)]⟩)
theorem product_checked : productCheck=true := by decide +kernel

def actualRow (index : Nat) : Row := ⟨[(output index,(p:Int)-1),(copy,1)],[]⟩
def actualRows : List Row := (List.range 5).map actualRow
def plainRows : List Row := actualRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
def normalizedRows : List Row := (List.range 5).map (fun index => ⟨[(0,1),(output index,-1)],[]⟩)
noncomputable def assertionCheck : Bool := (List.range 5).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+position index)=actualRows[index]?))
theorem assertion_checked : assertionCheck=true := by decide +kernel
noncomputable def reverseCheck : Bool := CompilerIndexed01.checkOriginalCoverage p 0
  plainRows.toArray normalizedRows.toArray (List.range 5).toArray
theorem reverse_checked : reverseCheck=true := by decide +kernel
noncomputable def soundCheck : Bool := (List.range 5).all (fun index =>
  Compiler.checkRow p plainRows ⟨subtract [(0,1)] [(output index,1)],[]⟩)
theorem sound_checked : soundCheck=true := by decide +kernel

variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (index : Nat) (bound : index<5) : rho (output index)=eval rho (operandTerms index)*rho (hintColumn index) := by
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
  simpa only [eval,Int.cast_one,one_mul,add_zero,mul_comm] using h

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+position index)) 5

theorem complete (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0) (values : ∀ index<5,rho (output index)=1) : Rows rho := by
  have normal : Satisfies rho normalizedRows := by
    intro row member
    obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
    have before : index<5 := List.mem_range.mp present
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
    (rows : Rows rho) (index : Nat) (bound : index<5) : eval rho (operandTerms index) ≠ 0 := by
  have actual : Satisfies rho actualRows := by
    intro row member
    obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp member
    have before : i<5 := by
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
end ShielddSecurity.CapturedAuthorizationShared419

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.operandTerms
#print axioms ShielddSecurity.CapturedAuthorizationShared419.operandTerms

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.hintColumn
#print axioms ShielddSecurity.CapturedAuthorizationShared419.hintColumn

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.arithmeticStart
#print axioms ShielddSecurity.CapturedAuthorizationShared419.arithmeticStart

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.position
#print axioms ShielddSecurity.CapturedAuthorizationShared419.position

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.output
#print axioms ShielddSecurity.CapturedAuthorizationShared419.output

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.rawRows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.rawRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.arithmeticRows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.arithmeticRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.arithmeticCheck
#print axioms ShielddSecurity.CapturedAuthorizationShared419.arithmeticCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.arithmetic_checked
#print axioms ShielddSecurity.CapturedAuthorizationShared419.arithmetic_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.productCheck
#print axioms ShielddSecurity.CapturedAuthorizationShared419.productCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.product_checked
#print axioms ShielddSecurity.CapturedAuthorizationShared419.product_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.actualRow
#print axioms ShielddSecurity.CapturedAuthorizationShared419.actualRow

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.actualRows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.actualRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.plainRows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.plainRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.normalizedRows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.normalizedRows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.assertionCheck
#print axioms ShielddSecurity.CapturedAuthorizationShared419.assertionCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.assertion_checked
#print axioms ShielddSecurity.CapturedAuthorizationShared419.assertion_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.reverseCheck
#print axioms ShielddSecurity.CapturedAuthorizationShared419.reverseCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.reverse_checked
#print axioms ShielddSecurity.CapturedAuthorizationShared419.reverse_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.soundCheck
#print axioms ShielddSecurity.CapturedAuthorizationShared419.soundCheck

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.sound_checked
#print axioms ShielddSecurity.CapturedAuthorizationShared419.sound_checked

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.products
#print axioms ShielddSecurity.CapturedAuthorizationShared419.products

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.Rows
#print axioms ShielddSecurity.CapturedAuthorizationShared419.Rows

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.complete
#print axioms ShielddSecurity.CapturedAuthorizationShared419.complete

set_option pp.all true in
#check @ShielddSecurity.CapturedAuthorizationShared419.sound
#print axioms ShielddSecurity.CapturedAuthorizationShared419.sound
