import ShielddSecurity.CapturedRegistryLowLimb130
import ShielddSecurity.ComparisonSound148
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedLowComparisonSound151
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
open CapturedRegistryLowLimb129
variable {F : Type} [Field F] [CharP F p]
theorem recipe_truth (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 131) (index : Nat) (bound : index<131) :
    Truth rho (expected index) :=
  (satisfies_iff copy 131 block rho linked).mp satisfied index bound (true,expected index) rfl
theorem bit_truth (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 131) (index : Nat) (bound : index<129) :
    Square (rho (if index=0 then 1112 else 1113+index))
      (rho (if index=0 then 1112 else 1113+index)) := by
  have h:=recipe_truth rho linked satisfied index (by omega)
  change Truth rho (if index<129 then _ else _) at h
  rw [if_pos bound] at h
  simpa only [Truth,sourceLeft,sourceRight,expressionValue,eval,Int.cast_one,one_mul,add_zero] using h
theorem reconstruction (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 131) :
    fieldBinary (columns.map rho)=rho 1113 := by
  have h:=recipe_truth rho linked satisfied 129 (by decide)
  change Truth rho (if 129<129 then _ else _) at h
  rw [if_neg (by decide),if_pos rfl] at h
  change eval rho (weighted columns 1)=eval rho [(1113,1)] at h
  simpa only [weighted_eval,Int.cast_one,one_mul,eval,add_zero] using h
theorem balance (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho block.actual 131) :
    fieldBinary (rightColumns.map rho)-fieldBinary (leftColumns.map rho)=
      rho 1113-rho 1112*(2^128:F) := by
  have h:=recipe_truth rho linked satisfied 130 (by decide)
  change Truth rho (if 130<129 then _ else _) at h
  rw [if_neg (by decide),if_neg (by decide)] at h
  change eval rho (weighted rightColumns 1++weighted leftColumns (-1))=
    eval rho [(1113,1),(1112,-(2^128))] at h
  calc
    _=eval rho (weighted rightColumns 1++weighted leftColumns (-1)) := by
      rw [eval_append,weighted_eval,weighted_eval];simp [sub_eq_add_neg]
    _=eval rho [(1113,1),(1112,-(2^128))] := h
    _=_ := by simp [eval];ring
theorem sound (rho : Nat → F) (a b : Nat) (left : a<2^128) (right : b<2^128)
    (leftMeaning : fieldBinary (leftColumns.map rho)=(a:F))
    (rightMeaning : fieldBinary (rightColumns.map rho)=(b:F))
    (linked : rho copy=rho 0) (satisfied : SatisfiesAt rho block.actual 131) :
    rho 1112=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) ∧
      rho 1113=(BoundedLimbComparison119.difference 128 a b:F) := by
  have booleanRows : ∀ x∈columns.map rho,Square x x := by
    intro x member
    obtain ⟨column,inColumns,rfl⟩:=List.mem_map.mp member
    change column∈List.range' 1114 128 at inColumns
    obtain ⟨offset,before,same⟩:=List.mem_range'.mp inColumns
    have sameIndex : column=1113+(offset+1) := by omega
    have h:=bit_truth rho linked satisfied (offset+1) (by omega)
    rw [if_neg (show ¬offset+1=0 by omega),←sameIndex] at h
    exact h
  obtain ⟨difference,bounded,value⟩:=range_sound (columns.map rho) (rho 1113) booleanRows
    (reconstruction rho linked satisfied)
  have exactBound : difference<2^128 := by simpa only [List.length_map,columns,List.length_range'] using bounded
  have h:=balance rho linked satisfied
  rw [leftMeaning,rightMeaning,←value] at h
  have booleanFlag:=boolean_sound (rho 1112) (by simpa only [if_true] using bit_truth rho linked satisfied 0 (by decide))
  have result:=ComparisonSound148.bounded_solution 128 a b difference (rho 1112) left right exactBound
    (by decide) booleanFlag h
  exact ⟨result.1,value.symm.trans (congrArg (fun n : Nat => (n:F)) result.2)⟩
end ShielddSecurity.CapturedLowComparisonSound151

set_option pp.all true in
#check @ShielddSecurity.CapturedLowComparisonSound151.recipe_truth
#print axioms ShielddSecurity.CapturedLowComparisonSound151.recipe_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedLowComparisonSound151.bit_truth
#print axioms ShielddSecurity.CapturedLowComparisonSound151.bit_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedLowComparisonSound151.reconstruction
#print axioms ShielddSecurity.CapturedLowComparisonSound151.reconstruction
set_option pp.all true in
#check @ShielddSecurity.CapturedLowComparisonSound151.balance
#print axioms ShielddSecurity.CapturedLowComparisonSound151.balance
set_option pp.all true in
#check @ShielddSecurity.CapturedLowComparisonSound151.sound
#print axioms ShielddSecurity.CapturedLowComparisonSound151.sound
