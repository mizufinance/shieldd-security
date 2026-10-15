-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.UserPathHash958C39
import ShielddSecurity.UserPathHash958C40
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSelector964RL01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨243370,false,[(1819,1)],[(1772,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(43220,1)],[(43221,1)],20482,[⟨[(1772,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1819,1),(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(43221,1)]⟩,⟨[(1772,1),(1819,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(43220,4),(43221,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(1819,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(1772,1)]++scaleLinear (-1) UserPathHash958C39.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43220=(rho 1819)*(rho 1772-eval rho UserPathHash958C39.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 43220 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨243373,false,[(1819,1)],[(1774,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(43222,1)],[(43223,1)],20484,[⟨[(1774,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1819,1),(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(43223,1)]⟩,⟨[(1774,1),(1819,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(43222,4),(43223,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(1819,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(1774,1)]++scaleLinear (-1) UserPathHash958C39.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43222=(rho 1819)*(rho 1774-eval rho UserPathHash958C39.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 43222 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨243382,false,[(1820,1)],[(1772,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289),(43220,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43224,1)],[(43225,1)],20486,[⟨[(1772,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1820,1),(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224),(43220,1)],[(43225,1)]⟩,⟨[(1772,1),(1820,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289),(43220,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43224,4),(43225,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(1820,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(1772,1),(43220,-1)]++scaleLinear (-1) UserPathHash958C39.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43224=(rho 1820)*(rho 1772-rho 43220-eval rho UserPathHash958C39.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 43224 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨243386,false,[(1820,1)],[(1772,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1773,1),(43220,1)],[(43226,1)],[(43227,1)],20488,[⟨[(1772,1),(1773,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1820,1),(43220,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43227,1)]⟩,⟨[(1772,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1773,1),(1820,1),(43220,1)],[(43226,4),(43227,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(1820,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(1773,1),(1772,-1),(43220,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43226=(rho 1820)*(rho 1773-rho 1772+rho 43220) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 43226 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨243390,false,[(1820,1)],[(1773,52435875175126190479447740508185965837690552500527637822603658699938581184512),(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224),(43222,1)],[(43228,1)],[(43229,1)],20490,[⟨[(1773,1),(1820,1),(43198,46855940266913453502209730394455508830783759657335420049550374818274958592832),(43202,1456928232331769666091604024043650394538239072306372778700000267793573709090),(43206,698131897170581497048307930565348753692375937666850051123327179522779327497),(43210,52155120632190118924124156561149583535786380164772322260000241192699256431877),(43214,7662113046484220376376826760560917990503811480570254258903603224694465574129),(43218,23883094150264385550751501831181724667314104799878138247322161948146534199289),(43222,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43229,1)]⟩,⟨[(1773,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1820,1),(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224),(43222,1)],[(43228,4),(43229,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(1820,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (UserPathHash958C39.result++[(43222,1),(1773,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43228=(rho 1820)*(eval rho UserPathHash958C39.result+rho 43222-rho 1773) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 43228 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨243394,false,[(1820,1)],[(43222,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43230,1)],[(43231,1)],20492,[⟨[(1820,1),(43222,1)],[(43231,1)]⟩,⟨[(1820,1),(43222,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(43230,4),(43231,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(1820,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(43222,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 43230=(rho 1820)*(-rho 43222) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 43230 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(43198,5579934908212736977238010113730457006906792843192217773053283881663622591681),(43202,50978946942794420813356136484142315443152313428221265043903658432145007475423),(43206,51737743277955608982399432577620617083998176562860787771480331520415801857016),(43210,280754542936071555323583947036382301904172335755315562603417507239324752636),(43214,44773762128641970103070913747625047847186741019957383563700055475244115610384),(43218,28552781024861804928696238677004241170376447700649499575281496751792046985224),(43220,1),(43224,1)]
theorem child0_shape : canonical p child0=canonical p (UserPathHash958C39.result++[(43220,1),(43224,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(1772,1),(43220,52435875175126190479447740508185965837690552500527637822603658699938581184512),(43226,1)]
theorem child1_shape : canonical p child1=canonical p ([(1772,1),(43220,-1),(43226,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(1773,1),(43228,1)]
theorem child2_shape : canonical p child2=canonical p ([(1773,1),(43228,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(1774,1),(43230,1)]
theorem child3_shape : canonical p child3=canonical p ([(1774,1),(43230,1)]) := by decide +kernel
theorem inputs_shape : UserPathHash958C40.inputs=[[(0,2)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 1819=BooleanHints207.bitValue lo) (high : rho 1820=BooleanHints207.bitValue hi) :
    UserPathHash958C40.inputs.map (eval rho)=[(2:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho UserPathHash958C39.result) (rho 1772) (rho 1773) (rho 1774) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,2)]=(2:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (2:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho UserPathHash958C39.result) (rho 1772) (rho 1773) (rho 1774)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.UserPathSelector964RL01

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.leftSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.leftSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL01.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.leftSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL01.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.leftSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL01.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.rightSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.rightSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL01.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.rightSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL01.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.rightSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL01.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select0_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.select0_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select0_left
#print axioms ShielddSecurity.UserPathSelector964RL01.select0_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select0_right
#print axioms ShielddSecurity.UserPathSelector964RL01.select0_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select0_value
#print axioms ShielddSecurity.UserPathSelector964RL01.select0_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select1_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.select1_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select1_left
#print axioms ShielddSecurity.UserPathSelector964RL01.select1_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select1_right
#print axioms ShielddSecurity.UserPathSelector964RL01.select1_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select1_value
#print axioms ShielddSecurity.UserPathSelector964RL01.select1_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select2_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.select2_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select2_left
#print axioms ShielddSecurity.UserPathSelector964RL01.select2_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select2_right
#print axioms ShielddSecurity.UserPathSelector964RL01.select2_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select2_value
#print axioms ShielddSecurity.UserPathSelector964RL01.select2_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select3_checked
#print axioms ShielddSecurity.UserPathSelector964RL01.select3_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select3_left
#print axioms ShielddSecurity.UserPathSelector964RL01.select3_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select3_right
#print axioms ShielddSecurity.UserPathSelector964RL01.select3_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.select3_value
#print axioms ShielddSecurity.UserPathSelector964RL01.select3_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.child0_shape
#print axioms ShielddSecurity.UserPathSelector964RL01.child0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.child1_shape
#print axioms ShielddSecurity.UserPathSelector964RL01.child1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.child2_shape
#print axioms ShielddSecurity.UserPathSelector964RL01.child2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.child3_shape
#print axioms ShielddSecurity.UserPathSelector964RL01.child3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.inputs_shape
#print axioms ShielddSecurity.UserPathSelector964RL01.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL01.input_values
#print axioms ShielddSecurity.UserPathSelector964RL01.input_values
