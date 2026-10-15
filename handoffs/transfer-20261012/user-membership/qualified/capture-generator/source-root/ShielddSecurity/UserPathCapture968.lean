-- GENERATED from maintained exact user-membership capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.UserPathHash958C37
import ShielddSecurity.UserPathHash958C54
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathCapture968
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
noncomputable def senderEntry : Entry := ⟨226419,false,[(10,1)],[(5,52435875175126190479447740508185965837690552500527637822603658699938581184512),(41604,5579934908212736977238010113730457006906792843192217773053283881663622591681),(41608,50978946942794420813356136484142315443152313428221265043903658432145007475423),(41612,51737743277955608982399432577620617083998176562860787771480331520415801857016),(41616,280754542936071555323583947036382301904172335755315562603417507239324752636),(41620,44773762128641970103070913747625047847186741019957383563700055475244115610384),(41624,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(41626,1)],[(41627,1)],18888,[⟨[(5,1),(10,1),(41604,46855940266913453502209730394455508830783759657335420049550374818274958592832),(41608,1456928232331769666091604024043650394538239072306372778700000267793573709090),(41612,698131897170581497048307930565348753692375937666850051123327179522779327497),(41616,52155120632190118924124156561149583535786380164772322260000241192699256431877),(41620,7662113046484220376376826760560917990503811480570254258903603224694465574129),(41624,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(41627,1)]⟩,⟨[(5,52435875175126190479447740508185965837690552500527637822603658699938581184512),(10,1),(41604,5579934908212736977238010113730457006906792843192217773053283881663622591681),(41608,50978946942794420813356136484142315443152313428221265043903658432145007475423),(41612,51737743277955608982399432577620617083998176562860787771480331520415801857016),(41616,280754542936071555323583947036382301904172335755315562603417507239324752636),(41620,44773762128641970103070913747625047847186741019957383563700055475244115610384),(41624,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(41626,4),(41627,1)]⟩]⟩
theorem sender_checked : check senderEntry=true := by decide +kernel
theorem sender_shape : canonical p senderEntry.right=canonical p (UserPathHash958C37.result++[(5,-1)]) := by decide +kernel
theorem sender_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 41626=rho 10*(eval rho UserPathHash958C37.result-rho 5) := by
  have result := MapArithmeticAdapter704.equation senderEntry sender_checked rho arithmetic
  have output : eval rho senderEntry.output=rho 41626 := by simp [senderEntry,eval]
  have square : senderEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ sender_shape,eval_append] at result
  simpa only [senderEntry,eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_one_mul,sub_eq_add_neg] using result
noncomputable def receiverEntry : Entry := ⟨324145,false,[(10,1)],[(5,52435875175126190479447740508185965837690552500527637822603658699938581184512),(49558,5579934908212736977238010113730457006906792843192217773053283881663622591681),(49562,50978946942794420813356136484142315443152313428221265043903658432145007475423),(49566,51737743277955608982399432577620617083998176562860787771480331520415801857016),(49570,280754542936071555323583947036382301904172335755315562603417507239324752636),(49574,44773762128641970103070913747625047847186741019957383563700055475244115610384),(49578,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(49580,1)],[(49581,1)],26842,[⟨[(5,1),(10,1),(49558,46855940266913453502209730394455508830783759657335420049550374818274958592832),(49562,1456928232331769666091604024043650394538239072306372778700000267793573709090),(49566,698131897170581497048307930565348753692375937666850051123327179522779327497),(49570,52155120632190118924124156561149583535786380164772322260000241192699256431877),(49574,7662113046484220376376826760560917990503811480570254258903603224694465574129),(49578,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(49581,1)]⟩,⟨[(5,52435875175126190479447740508185965837690552500527637822603658699938581184512),(10,1),(49558,5579934908212736977238010113730457006906792843192217773053283881663622591681),(49562,50978946942794420813356136484142315443152313428221265043903658432145007475423),(49566,51737743277955608982399432577620617083998176562860787771480331520415801857016),(49570,280754542936071555323583947036382301904172335755315562603417507239324752636),(49574,44773762128641970103070913747625047847186741019957383563700055475244115610384),(49578,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(49580,4),(49581,1)]⟩]⟩
theorem receiver_checked : check receiverEntry=true := by decide +kernel
theorem receiver_shape : canonical p receiverEntry.right=canonical p (UserPathHash958C54.result++[(5,-1)]) := by decide +kernel
theorem receiver_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 49580=rho 10*(eval rho UserPathHash958C54.result-rho 5) := by
  have result := MapArithmeticAdapter704.equation receiverEntry receiver_checked rho arithmetic
  have output : eval rho receiverEntry.output=rho 49580 := by simp [receiverEntry,eval]
  have square : receiverEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ receiver_shape,eval_append] at result
  simpa only [receiverEntry,eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_one_mul,sub_eq_add_neg] using result
noncomputable def row1524 : Row := ⟨[(41626,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row1524_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+1524) 1 [row1524]=true := by decide +kernel

theorem row1524_satisfies (rho : Nat → F) (zero : rho 41626=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1524+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row1524] row1524_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(41626,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(41626,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
noncomputable def row1779 : Row := ⟨[(49580,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row1779_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+1779) 1 [row1779]=true := by decide +kernel

theorem row1779_satisfies (rho : Nat → F) (zero : rho 49580=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1779+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row1779] row1779_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(49580,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(49580,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1524+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1779+i)) 1

theorem rows (rho : Nat → F) (sender : rho 41626=0) (receiver : rho 49580=0) : Rows rho :=
  ⟨row1524_satisfies rho sender,row1779_satisfies rho receiver⟩
end ShielddSecurity.UserPathCapture968

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.sender_checked
#print axioms ShielddSecurity.UserPathCapture968.sender_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.sender_shape
#print axioms ShielddSecurity.UserPathCapture968.sender_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.sender_value
#print axioms ShielddSecurity.UserPathCapture968.sender_value

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.receiver_checked
#print axioms ShielddSecurity.UserPathCapture968.receiver_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.receiver_shape
#print axioms ShielddSecurity.UserPathCapture968.receiver_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.receiver_value
#print axioms ShielddSecurity.UserPathCapture968.receiver_value

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.row1524_captured
#print axioms ShielddSecurity.UserPathCapture968.row1524_captured

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.row1524_satisfies
#print axioms ShielddSecurity.UserPathCapture968.row1524_satisfies

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.row1779_captured
#print axioms ShielddSecurity.UserPathCapture968.row1779_captured

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.row1779_satisfies
#print axioms ShielddSecurity.UserPathCapture968.row1779_satisfies

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.Rows
#print axioms ShielddSecurity.UserPathCapture968.Rows

set_option pp.all true in
#check @ShielddSecurity.UserPathCapture968.rows
#print axioms ShielddSecurity.UserPathCapture968.rows
