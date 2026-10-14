-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.VolumePriorHash908
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorCapture910
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def continuationEntry : Entry := ⟨779860,false,[(7605,1)],[(7606,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(109326,1)],[(109327,1)],86588,[⟨[(7605,1),(7606,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109327,1)]⟩,⟨[(7605,1),(7606,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(109326,4),(109327,1)]⟩]⟩
theorem continuation_checked : check continuationEntry=true := by decide +kernel
theorem continuation_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109326=eval rho [(7605,1)]*eval rho [(7606,-1),(200692,1)] := by
  have result := MapArithmeticAdapter704.equation continuationEntry continuation_checked rho arithmetic
  have left : canonical p [(7605,1)]=canonical p [(7605,1)] := by decide +kernel
  have right : canonical p [(7606,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)]=canonical p [(7606,-1),(200692,1)] := by decide +kernel
  simp only [continuationEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def priorEntry : Entry := ⟨779863,false,[(109326,1)],[(8386,1),(109304,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109308,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109312,698131897170581497048307930565348753692375937666850051123327179522779327497),(109316,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109320,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109324,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(109328,1)],[(109329,1)],86590,[⟨[(8386,52435875175126190479447740508185965837690552500527637822603658699938581184512),(109304,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109312,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109316,280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109324,28552781024861804928696238677004241170376447700649499575281496751792046985224),(109326,1)],[(109329,1)]⟩,⟨[(8386,1),(109304,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109308,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109312,698131897170581497048307930565348753692375937666850051123327179522779327497),(109316,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109320,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109324,23883094150264385550751501831181724667314104799878138247322161948146534199289),(109326,1)],[(109328,4),(109329,1)]⟩]⟩
theorem prior_checked : check priorEntry=true := by decide +kernel
theorem prior_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109328=eval rho [(109326,1)]*eval rho [(8386,1),(109304,-5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109312,698131897170581497048307930565348753692375937666850051123327179522779327497),(109316,-280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109324,23883094150264385550751501831181724667314104799878138247322161948146534199289)] := by
  have result := MapArithmeticAdapter704.equation priorEntry prior_checked rho arithmetic
  have left : canonical p [(109326,1)]=canonical p [(109326,1)] := by decide +kernel
  have right : canonical p [(8386,1),(109304,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109308,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109312,698131897170581497048307930565348753692375937666850051123327179522779327497),(109316,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109320,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109324,23883094150264385550751501831181724667314104799878138247322161948146534199289)]=canonical p [(8386,1),(109304,-5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109312,698131897170581497048307930565348753692375937666850051123327179522779327497),(109316,-280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109324,23883094150264385550751501831181724667314104799878138247322161948146534199289)] := by decide +kernel
  simp only [priorEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
theorem prior_shape : canonical p priorEntry.right=canonical p ([(8386,1)]++scaleLinear (-1) VolumePriorHash908.result) := by decide +kernel
theorem prior_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109328=rho 109326*(rho 8386-eval rho VolumePriorHash908.result) := by
  have result := MapArithmeticAdapter704.equation priorEntry prior_checked rho arithmetic
  have output : eval rho priorEntry.output=rho 109328 := by simp [priorEntry,eval]
  have square : priorEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ prior_shape,eval_append,eval_scale] at result
  simpa only [priorEntry,eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_one_mul,sub_eq_add_neg] using result
theorem continuation_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109326=rho 7605*(rho copy-rho 7606) := by
  have result := continuation_equation rho arithmetic
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,copy,sub_eq_add_neg,add_comm] using result
noncomputable def row8264 : Row := ⟨[(109328,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8264_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8264) 1 [row8264]=true := by decide +kernel

theorem row8264_satisfies (rho : Nat → F) (zero : rho 109328=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8264+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8264] row8264_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(109328,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(109328,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8264+i)) 1

theorem rows (rho : Nat → F) (prior : rho 109328=0) : Rows rho :=
  row8264_satisfies rho prior
end ShielddSecurity.VolumePriorCapture910

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.continuation_checked
#print axioms ShielddSecurity.VolumePriorCapture910.continuation_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.continuation_equation
#print axioms ShielddSecurity.VolumePriorCapture910.continuation_equation

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.prior_checked
#print axioms ShielddSecurity.VolumePriorCapture910.prior_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.prior_equation
#print axioms ShielddSecurity.VolumePriorCapture910.prior_equation

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.prior_shape
#print axioms ShielddSecurity.VolumePriorCapture910.prior_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.prior_value
#print axioms ShielddSecurity.VolumePriorCapture910.prior_value

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.continuation_value
#print axioms ShielddSecurity.VolumePriorCapture910.continuation_value

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.row8264_captured
#print axioms ShielddSecurity.VolumePriorCapture910.row8264_captured

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.row8264_satisfies
#print axioms ShielddSecurity.VolumePriorCapture910.row8264_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.Rows
#print axioms ShielddSecurity.VolumePriorCapture910.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumePriorCapture910.rows
#print axioms ShielddSecurity.VolumePriorCapture910.rows
