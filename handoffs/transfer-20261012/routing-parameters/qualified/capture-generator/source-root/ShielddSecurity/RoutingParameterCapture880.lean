-- GENERATED. Edit maintained generator.
import ShielddSecurity.RoutingParameterHash878
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterCapture880
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def row : Row := ⟨[(19589,52435875175126190479447740508185965837690552500527637822603658699938581184512),(184843,5579934908212736977238010113730457006906792843192217773053283881663622591681),(184847,50978946942794420813356136484142315443152313428221265043903658432145007475423),(184851,51737743277955608982399432577620617083998176562860787771480331520415801857016),(184855,280754542936071555323583947036382301904172335755315562603417507239324752636),(184859,44773762128641970103070913747625047847186741019957383563700055475244115610384),(184863,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[]⟩
theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+19539) 1 [row]=true := by decide +kernel
theorem shape : canonical p row.a=canonical p (RoutingParameterHash878.result++[(19589,-1)]) := by decide +kernel
def Rows (rho : Nat → F) : Prop := SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19539+i)) 1
theorem rows (rho : Nat → F) (meaning : eval rho RoutingParameterHash878.result=rho 19589) : Rows rho := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row] captured rho).mp
  intro selected member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst selected
  have value : eval rho row.a=0 := by
    rw [canonical_equal rho _ _ shape,eval_append,meaning]
    simp [eval]
  change eval rho row.a*eval rho row.a=eval rho []
  simp only [value,mul_zero,eval]
end ShielddSecurity.RoutingParameterCapture880

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterCapture880.captured
#print axioms ShielddSecurity.RoutingParameterCapture880.captured

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterCapture880.shape
#print axioms ShielddSecurity.RoutingParameterCapture880.shape

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterCapture880.Rows
#print axioms ShielddSecurity.RoutingParameterCapture880.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterCapture880.rows
#print axioms ShielddSecurity.RoutingParameterCapture880.rows
