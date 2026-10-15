-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.UserPathHash958C52
import ShielddSecurity.UserPathHash958C53
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSelector964RL14
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨313375,false,[(1845,1)],[(1811,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(48732,1)],[(48733,1)],25994,[⟨[(1811,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1845,1),(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(48733,1)]⟩,⟨[(1811,1),(1845,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(48732,4),(48733,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(1845,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(1811,1)]++scaleLinear (-1) UserPathHash958C52.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48732=(rho 1845)*(rho 1811-eval rho UserPathHash958C52.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 48732 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨313378,false,[(1845,1)],[(1813,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(48734,1)],[(48735,1)],25996,[⟨[(1813,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1845,1),(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(48735,1)]⟩,⟨[(1813,1),(1845,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(48734,4),(48735,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(1845,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(1813,1)]++scaleLinear (-1) UserPathHash958C52.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48734=(rho 1845)*(rho 1813-eval rho UserPathHash958C52.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 48734 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨313387,false,[(1846,1)],[(1811,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289),(48732,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48736,1)],[(48737,1)],25998,[⟨[(1811,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1846,1),(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224),(48732,1)],[(48737,1)]⟩,⟨[(1811,1),(1846,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289),(48732,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48736,4),(48737,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(1846,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(1811,1),(48732,-1)]++scaleLinear (-1) UserPathHash958C52.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48736=(rho 1846)*(rho 1811-rho 48732-eval rho UserPathHash958C52.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 48736 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨313391,false,[(1846,1)],[(1811,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1812,1),(48732,1)],[(48738,1)],[(48739,1)],26000,[⟨[(1811,1),(1812,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1846,1),(48732,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48739,1)]⟩,⟨[(1811,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1812,1),(1846,1),(48732,1)],[(48738,4),(48739,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(1846,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(1812,1),(1811,-1),(48732,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48738=(rho 1846)*(rho 1812-rho 1811+rho 48732) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 48738 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨313395,false,[(1846,1)],[(1812,52435875175126190479447740508185965837690552500527637822603658699938581184512),(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224),(48734,1)],[(48740,1)],[(48741,1)],26002,[⟨[(1812,1),(1846,1),(48710,46855940266913453502209730394455508830783759657335420049550374818274958592832),(48714,1456928232331769666091604024043650394538239072306372778700000267793573709090),(48718,698131897170581497048307930565348753692375937666850051123327179522779327497),(48722,52155120632190118924124156561149583535786380164772322260000241192699256431877),(48726,7662113046484220376376826760560917990503811480570254258903603224694465574129),(48730,23883094150264385550751501831181724667314104799878138247322161948146534199289),(48734,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48741,1)]⟩,⟨[(1812,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1846,1),(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224),(48734,1)],[(48740,4),(48741,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(1846,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (UserPathHash958C52.result++[(48734,1),(1812,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48740=(rho 1846)*(eval rho UserPathHash958C52.result+rho 48734-rho 1812) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 48740 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨313399,false,[(1846,1)],[(48734,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48742,1)],[(48743,1)],26004,[⟨[(1846,1),(48734,1)],[(48743,1)]⟩,⟨[(1846,1),(48734,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(48742,4),(48743,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(1846,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(48734,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 48742=(rho 1846)*(-rho 48734) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 48742 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(48710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(48714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(48718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(48722,280754542936071555323583947036382301904172335755315562603417507239324752636),(48726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(48730,28552781024861804928696238677004241170376447700649499575281496751792046985224),(48732,1),(48736,1)]
theorem child0_shape : canonical p child0=canonical p (UserPathHash958C52.result++[(48732,1),(48736,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(1811,1),(48732,52435875175126190479447740508185965837690552500527637822603658699938581184512),(48738,1)]
theorem child1_shape : canonical p child1=canonical p ([(1811,1),(48732,-1),(48738,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(1812,1),(48740,1)]
theorem child2_shape : canonical p child2=canonical p ([(1812,1),(48740,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(1813,1),(48742,1)]
theorem child3_shape : canonical p child3=canonical p ([(1813,1),(48742,1)]) := by decide +kernel
theorem inputs_shape : UserPathHash958C53.inputs=[[(0,15)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 1845=BooleanHints207.bitValue lo) (high : rho 1846=BooleanHints207.bitValue hi) :
    UserPathHash958C53.inputs.map (eval rho)=[(15:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho UserPathHash958C52.result) (rho 1811) (rho 1812) (rho 1813) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,15)]=(15:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (15:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho UserPathHash958C52.result) (rho 1811) (rho 1812) (rho 1813)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.UserPathSelector964RL14

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.leftSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.leftSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL14.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.leftSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL14.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.leftSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL14.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.rightSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.rightSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL14.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.rightSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL14.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.rightSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL14.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select0_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.select0_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select0_left
#print axioms ShielddSecurity.UserPathSelector964RL14.select0_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select0_right
#print axioms ShielddSecurity.UserPathSelector964RL14.select0_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select0_value
#print axioms ShielddSecurity.UserPathSelector964RL14.select0_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select1_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.select1_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select1_left
#print axioms ShielddSecurity.UserPathSelector964RL14.select1_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select1_right
#print axioms ShielddSecurity.UserPathSelector964RL14.select1_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select1_value
#print axioms ShielddSecurity.UserPathSelector964RL14.select1_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select2_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.select2_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select2_left
#print axioms ShielddSecurity.UserPathSelector964RL14.select2_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select2_right
#print axioms ShielddSecurity.UserPathSelector964RL14.select2_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select2_value
#print axioms ShielddSecurity.UserPathSelector964RL14.select2_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select3_checked
#print axioms ShielddSecurity.UserPathSelector964RL14.select3_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select3_left
#print axioms ShielddSecurity.UserPathSelector964RL14.select3_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select3_right
#print axioms ShielddSecurity.UserPathSelector964RL14.select3_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.select3_value
#print axioms ShielddSecurity.UserPathSelector964RL14.select3_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.child0_shape
#print axioms ShielddSecurity.UserPathSelector964RL14.child0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.child1_shape
#print axioms ShielddSecurity.UserPathSelector964RL14.child1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.child2_shape
#print axioms ShielddSecurity.UserPathSelector964RL14.child2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.child3_shape
#print axioms ShielddSecurity.UserPathSelector964RL14.child3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.inputs_shape
#print axioms ShielddSecurity.UserPathSelector964RL14.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL14.input_values
#print axioms ShielddSecurity.UserPathSelector964RL14.input_values
