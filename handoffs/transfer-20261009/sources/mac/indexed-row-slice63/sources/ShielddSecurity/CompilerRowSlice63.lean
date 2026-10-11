import ShielddSecurity.CompilerAssertionBlock51
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerRowSlice63
open CompilerAssertionBlock51

def check (parent : Nat → Option Row) (start length : Nat) (actual : List Row) : Bool :=
  decide (actual.length=length) &&
  (List.range length).all (fun index => decide (parent (start+index)=actual[index]?))
theorem count (parent : Nat → Option Row) (start length : Nat) (actual : List Row)
    (checked : check parent start length actual=true) : actual.length=length :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
theorem position (parent : Nat → Option Row) (start length : Nat) (actual : List Row)
    (checked : check parent start length actual=true) (index : Nat) (bound : index<length) :
    parent (start+index)=actual[index]? := by
  have h:=List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 index (List.mem_range.mpr bound)
  exact of_decide_eq_true h
theorem every_position (parent : Nat → Option Row) (start length : Nat) (actual : List Row)
    (checked : check parent start length actual=true) (index : Nat) (bound : index<length) :
    ∃ row,parent (start+index)=some row := by
  have before : index<actual.length := by rw [count parent start length actual checked];exact bound
  refine ⟨actual[index],?_⟩
  rw [position parent start length actual checked index bound]
  exact List.getElem?_eq_getElem before
variable {F : Type} [Field F]
theorem list_indexed_iff (rho : Nat → F) (actual : List Row) :
    Satisfies rho actual ↔ SatisfiesAt rho (fun index => actual[index]?) actual.length := by
  constructor
  · intro sat index bound row found
    exact sat row (List.mem_iff_getElem?.mpr ⟨index,found⟩)
  · intro sat row member
    obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
    obtain ⟨bound,_⟩:=List.getElem?_eq_some_iff.mp found
    exact sat index bound row found

theorem selected_satisfies_iff (parent : Nat → Option Row) (start length : Nat)
    (actual : List Row) (checked : check parent start length actual=true) (rho : Nat → F) :
    Satisfies rho actual ↔ SatisfiesAt rho (fun index => parent (start+index)) length := by
  rw [list_indexed_iff rho actual,count parent start length actual checked]
  constructor
  · intro sat index bound row found
    apply sat index bound row
    exact (position parent start length actual checked index bound).symm.trans found
  · intro sat index bound row found
    apply sat index bound row
    exact (position parent start length actual checked index bound).trans found

theorem of_full_satisfies (parent : Nat → Option Row) (fullLength start length : Nat)
    (actual : List Row) (checked : check parent start length actual=true)
    (inside : start+length≤fullLength) (rho : Nat → F)
    (sat : SatisfiesAt rho parent fullLength) : Satisfies rho actual := by
  apply (selected_satisfies_iff parent start length actual checked rho).mpr
  intro index bound row found
  exact sat (start+index) (by omega) row found

theorem of_full_indexed (parent : Nat → Option Row) (fullLength start length : Nat)
    (actual : List Row) (checked : check parent start length actual=true)
    (inside : start+length≤fullLength) (rho : Nat → F)
    (sat : SatisfiesAt rho parent fullLength) :
    SatisfiesAt rho (fun index => actual[index]?) length := by
  have localRows:=of_full_satisfies parent fullLength start length actual checked inside rho sat
  have indexed:=(list_indexed_iff rho actual).mp localRows
  simpa only [count parent start length actual checked] using indexed
end ShielddSecurity.CompilerRowSlice63

set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.check
#print axioms ShielddSecurity.CompilerRowSlice63.check
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.count
#print axioms ShielddSecurity.CompilerRowSlice63.count
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.position
#print axioms ShielddSecurity.CompilerRowSlice63.position
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.every_position
#print axioms ShielddSecurity.CompilerRowSlice63.every_position
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.list_indexed_iff
#print axioms ShielddSecurity.CompilerRowSlice63.list_indexed_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.selected_satisfies_iff
#print axioms ShielddSecurity.CompilerRowSlice63.selected_satisfies_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.of_full_satisfies
#print axioms ShielddSecurity.CompilerRowSlice63.of_full_satisfies
set_option pp.all true in
#check @ShielddSecurity.CompilerRowSlice63.of_full_indexed
#print axioms ShielddSecurity.CompilerRowSlice63.of_full_indexed
