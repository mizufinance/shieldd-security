-- GENERATED from the maintained exact public-statement capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.PublicStatementHash977C187
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementCapture997
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
noncomputable def row : Row := ⟨[(22737,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200670,5579934908212736977238010113730457006906792843192217773053283881663622591681),(200674,50978946942794420813356136484142315443152313428221265043903658432145007475423),(200678,51737743277955608982399432577620617083998176562860787771480331520415801857016),(200682,280754542936071555323583947036382301904172335755315562603417507239324752636),(200686,44773762128641970103070913747625047847186741019957383563700055475244115610384),(200690,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[]⟩
theorem row_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+22812) 1 [row]=true := by decide +kernel

theorem row_shape : canonical p row.a=canonical p (PublicStatementHash977C187.result++[(22737,-1)]) := by decide +kernel

theorem row_value (rho : Nat → F) : eval rho row.a=eval rho PublicStatementHash977C187.result-rho 22737 := by
  rw [canonical_equal rho _ _ row_shape,eval_append]
  simp only [eval,Int.cast_neg,Int.cast_one,neg_one_mul,add_zero,sub_eq_add_neg]

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22812+i)) 1

theorem rows (rho : Nat → F) (claimed : eval rho PublicStatementHash977C187.result=rho 22737) : Rows rho := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row] row_captured rho).mp
  intro selected member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst selected
  change eval rho row.a*eval rho row.a=eval rho []
  rw [row_value,claimed,sub_self]
  simp only [zero_mul,eval]
end ShielddSecurity.PublicStatementCapture997

set_option pp.all true in
#check @ShielddSecurity.PublicStatementCapture997.row_captured
#print axioms ShielddSecurity.PublicStatementCapture997.row_captured

set_option pp.all true in
#check @ShielddSecurity.PublicStatementCapture997.row_shape
#print axioms ShielddSecurity.PublicStatementCapture997.row_shape

set_option pp.all true in
#check @ShielddSecurity.PublicStatementCapture997.row_value
#print axioms ShielddSecurity.PublicStatementCapture997.row_value

set_option pp.all true in
#check @ShielddSecurity.PublicStatementCapture997.Rows
#print axioms ShielddSecurity.PublicStatementCapture997.Rows

set_option pp.all true in
#check @ShielddSecurity.PublicStatementCapture997.rows
#print axioms ShielddSecurity.PublicStatementCapture997.rows
