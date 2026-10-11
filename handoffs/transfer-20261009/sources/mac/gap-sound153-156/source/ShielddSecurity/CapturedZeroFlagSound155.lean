import ShielddSecurity.CapturedHighZero126
import ShielddSecurity.CapturedNextHighZero138
import ShielddSecurity.ComparisonSound148
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedZeroFlagSound155
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem first_truth (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (index : Nat) (bound : index<3) : Truth rho (CapturedHighZero126.expected index) := by
  have actual : SatisfiesAt rho CapturedHighZero126.block.actual 3 := by
    intro i before row found
    apply satisfied (179023+i) (by omega) row
    rw [CapturedHighZero126.assertion_position i before]
    exact found
  exact (satisfies_iff copy 3 CapturedHighZero126.block rho
    (CapturedFullRelation58.verifier_links rho satisfied).2.2).mp actual index bound
      (true,CapturedHighZero126.expected index) rfl
theorem first_flag (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) : rho 1110=FieldZeroSeed125.flag (eval rho CapturedHighZero126.delta) := by
  have products:=CapturedHighZero126.products rho ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1
  have unit:=first_truth rho satisfied 1 (by decide)
  change eval rho [(33770,1),(1110,1)]=eval rho [(0,1)] at unit
  simp only [eval,Int.cast_one,one_mul,add_zero] at unit
  rw [products.1,one] at unit
  have annihilated:=first_truth rho satisfied 2 (by decide)
  change eval rho []=eval rho [(33772,1)] at annihilated
  simp only [eval,Int.cast_one,one_mul,add_zero] at annihilated
  exact ComparisonSound148.zero_flag (eval rho CapturedHighZero126.delta) (rho 1111) (rho 1110) unit
    (products.2.symm.trans annihilated.symm)
omit [CharP F p] in
theorem first_delta (rho : Nat → F) : eval rho CapturedHighZero126.delta=
    fieldBinary (CapturedRegistryHighLimb120.leftColumns.map rho)-fieldBinary (CapturedRegistryHighLimb120.rightColumns.map rho) := by
  change eval rho (weighted CapturedRegistryHighLimb120.rightColumns (-1)++weighted CapturedRegistryHighLimb120.leftColumns 1)=_
  rw [eval_append,weighted_eval,weighted_eval]
  simp [sub_eq_add_neg];ring
theorem next_truth (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (index : Nat) (bound : index<3) : Truth rho (CapturedNextHighZero138.expected index) := by
  have actual : SatisfiesAt rho CapturedNextHighZero138.block.actual 3 := by
    intro i before row found
    apply satisfied (179287+i) (by omega) row
    rw [CapturedNextHighZero138.assertion_position i before]
    exact found
  exact (satisfies_iff copy 3 CapturedNextHighZero138.block rho
    (CapturedFullRelation58.verifier_links rho satisfied).2.2).mp actual index bound
      (true,CapturedNextHighZero138.expected index) rfl
theorem next_flag (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (one : rho 0=1) : rho 1371=FieldZeroSeed125.flag (eval rho CapturedNextHighZero138.delta) := by
  have products:=CapturedNextHighZero138.products rho ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1
  have unit:=next_truth rho satisfied 1 (by decide)
  change eval rho [(33778,1),(1371,1)]=eval rho [(0,1)] at unit
  simp only [eval,Int.cast_one,one_mul,add_zero] at unit
  rw [products.1,one] at unit
  have annihilated:=next_truth rho satisfied 2 (by decide)
  change eval rho []=eval rho [(33780,1)] at annihilated
  simp only [eval,Int.cast_one,one_mul,add_zero] at annihilated
  exact ComparisonSound148.zero_flag (eval rho CapturedNextHighZero138.delta) (rho 1372) (rho 1371) unit
    (products.2.symm.trans annihilated.symm)
omit [CharP F p] in
theorem next_delta (rho : Nat → F) : eval rho CapturedNextHighZero138.delta=
    fieldBinary (CapturedNextHighLimb133.leftColumns.map rho)-fieldBinary (CapturedNextHighLimb133.rightColumns.map rho) := by
  change eval rho (weighted CapturedNextHighLimb133.rightColumns (-1)++weighted CapturedNextHighLimb133.leftColumns 1)=_
  rw [eval_append,weighted_eval,weighted_eval]
  simp [sub_eq_add_neg];ring
end ShielddSecurity.CapturedZeroFlagSound155

set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.first_truth
#print axioms ShielddSecurity.CapturedZeroFlagSound155.first_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.first_flag
#print axioms ShielddSecurity.CapturedZeroFlagSound155.first_flag
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.first_delta
#print axioms ShielddSecurity.CapturedZeroFlagSound155.first_delta
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.next_truth
#print axioms ShielddSecurity.CapturedZeroFlagSound155.next_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.next_flag
#print axioms ShielddSecurity.CapturedZeroFlagSound155.next_flag
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroFlagSound155.next_delta
#print axioms ShielddSecurity.CapturedZeroFlagSound155.next_delta
