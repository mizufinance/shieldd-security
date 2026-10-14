-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.VolumePathHash931C148
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathCapture950
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
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
noncomputable def membershipEntry : Entry := ⟨909346,false,[(109326,1)],[(3,52435875175126190479447740508185965837690552500527637822603658699938581184512),(119484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(119488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(119492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(119496,280754542936071555323583947036382301904172335755315562603417507239324752636),(119500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(119504,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(119506,1)],[(119507,1)],96768,[⟨[(3,1),(109326,1),(119484,46855940266913453502209730394455508830783759657335420049550374818274958592832),(119488,1456928232331769666091604024043650394538239072306372778700000267793573709090),(119492,698131897170581497048307930565348753692375937666850051123327179522779327497),(119496,52155120632190118924124156561149583535786380164772322260000241192699256431877),(119500,7662113046484220376376826760560917990503811480570254258903603224694465574129),(119504,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(119507,1)]⟩,⟨[(3,52435875175126190479447740508185965837690552500527637822603658699938581184512),(109326,1),(119484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(119488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(119492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(119496,280754542936071555323583947036382301904172335755315562603417507239324752636),(119500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(119504,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(119506,4),(119507,1)]⟩]⟩
theorem membership_checked : check membershipEntry=true := by decide +kernel
theorem membership_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 119506=eval rho [(109326,1)]*eval rho [(3,-1),(119484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(119488,-1456928232331769666091604024043650394538239072306372778700000267793573709090),(119492,-698131897170581497048307930565348753692375937666850051123327179522779327497),(119496,280754542936071555323583947036382301904172335755315562603417507239324752636),(119500,-7662113046484220376376826760560917990503811480570254258903603224694465574129),(119504,-23883094150264385550751501831181724667314104799878138247322161948146534199289)] := by
  have result := MapArithmeticAdapter704.equation membershipEntry membership_checked rho arithmetic
  have left : canonical p [(109326,1)]=canonical p [(109326,1)] := by decide +kernel
  have right : canonical p [(3,52435875175126190479447740508185965837690552500527637822603658699938581184512),(119484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(119488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(119492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(119496,280754542936071555323583947036382301904172335755315562603417507239324752636),(119500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(119504,28552781024861804928696238677004241170376447700649499575281496751792046985224)]=canonical p [(3,-1),(119484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(119488,-1456928232331769666091604024043650394538239072306372778700000267793573709090),(119492,-698131897170581497048307930565348753692375937666850051123327179522779327497),(119496,280754542936071555323583947036382301904172335755315562603417507239324752636),(119500,-7662113046484220376376826760560917990503811480570254258903603224694465574129),(119504,-23883094150264385550751501831181724667314104799878138247322161948146534199289)] := by decide +kernel
  simp only [membershipEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
theorem membership_shape : canonical p membershipEntry.right=canonical p (VolumePathHash931C148.result++[(3,-1)]) := by decide +kernel
theorem membership_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 119506=rho 109326*(eval rho VolumePathHash931C148.result-rho 3) := by
  have result := MapArithmeticAdapter704.equation membershipEntry membership_checked rho arithmetic
  have output : eval rho membershipEntry.output=rho 119506 := by simp [membershipEntry,eval]
  have square : membershipEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ membership_shape,eval_append] at result
  simpa only [membershipEntry,eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_one_mul,sub_eq_add_neg] using result
theorem continuation_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109326=rho 7605*(rho copy-rho 7606) := by
  have result := continuation_equation rho arithmetic
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,zero_add,add_zero,neg_mul,copy,sub_eq_add_neg,add_comm] using result
noncomputable def row8315 : Row := ⟨[(119506,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8315_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8315) 1 [row8315]=true := by decide +kernel

theorem row8315_satisfies (rho : Nat → F) (zero : rho 119506=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8315+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8315] row8315_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(119506,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(119506,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8315+i)) 1

theorem rows (rho : Nat → F) (prior : rho 119506=0) : Rows rho :=
  row8315_satisfies rho prior
end ShielddSecurity.VolumePathCapture950

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.continuation_checked
#print axioms ShielddSecurity.VolumePathCapture950.continuation_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.continuation_equation
#print axioms ShielddSecurity.VolumePathCapture950.continuation_equation

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.membership_checked
#print axioms ShielddSecurity.VolumePathCapture950.membership_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.membership_equation
#print axioms ShielddSecurity.VolumePathCapture950.membership_equation

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.membership_shape
#print axioms ShielddSecurity.VolumePathCapture950.membership_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.membership_value
#print axioms ShielddSecurity.VolumePathCapture950.membership_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.continuation_value
#print axioms ShielddSecurity.VolumePathCapture950.continuation_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.row8315_captured
#print axioms ShielddSecurity.VolumePathCapture950.row8315_captured

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.row8315_satisfies
#print axioms ShielddSecurity.VolumePathCapture950.row8315_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.Rows
#print axioms ShielddSecurity.VolumePathCapture950.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumePathCapture950.rows
#print axioms ShielddSecurity.VolumePathCapture950.rows
