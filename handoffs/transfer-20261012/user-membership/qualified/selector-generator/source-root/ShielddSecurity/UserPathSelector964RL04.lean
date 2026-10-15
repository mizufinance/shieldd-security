-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.UserPathHash958C42
import ShielddSecurity.UserPathHash958C43
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSelector964RL04
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨259525,false,[(1825,1)],[(1781,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(44492,1)],[(44493,1)],21754,[⟨[(1781,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1825,1),(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(44493,1)]⟩,⟨[(1781,1),(1825,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(44492,4),(44493,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(1825,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(1781,1)]++scaleLinear (-1) UserPathHash958C42.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44492=(rho 1825)*(rho 1781-eval rho UserPathHash958C42.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 44492 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨259528,false,[(1825,1)],[(1783,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(44494,1)],[(44495,1)],21756,[⟨[(1783,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1825,1),(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(44495,1)]⟩,⟨[(1783,1),(1825,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(44494,4),(44495,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(1825,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(1783,1)]++scaleLinear (-1) UserPathHash958C42.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44494=(rho 1825)*(rho 1783-eval rho UserPathHash958C42.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 44494 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨259537,false,[(1826,1)],[(1781,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289),(44492,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44496,1)],[(44497,1)],21758,[⟨[(1781,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1826,1),(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224),(44492,1)],[(44497,1)]⟩,⟨[(1781,1),(1826,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289),(44492,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44496,4),(44497,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(1826,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(1781,1),(44492,-1)]++scaleLinear (-1) UserPathHash958C42.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44496=(rho 1826)*(rho 1781-rho 44492-eval rho UserPathHash958C42.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 44496 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨259541,false,[(1826,1)],[(1781,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1782,1),(44492,1)],[(44498,1)],[(44499,1)],21760,[⟨[(1781,1),(1782,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1826,1),(44492,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44499,1)]⟩,⟨[(1781,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1782,1),(1826,1),(44492,1)],[(44498,4),(44499,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(1826,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(1782,1),(1781,-1),(44492,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44498=(rho 1826)*(rho 1782-rho 1781+rho 44492) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 44498 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨259545,false,[(1826,1)],[(1782,52435875175126190479447740508185965837690552500527637822603658699938581184512),(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224),(44494,1)],[(44500,1)],[(44501,1)],21762,[⟨[(1782,1),(1826,1),(44470,46855940266913453502209730394455508830783759657335420049550374818274958592832),(44474,1456928232331769666091604024043650394538239072306372778700000267793573709090),(44478,698131897170581497048307930565348753692375937666850051123327179522779327497),(44482,52155120632190118924124156561149583535786380164772322260000241192699256431877),(44486,7662113046484220376376826760560917990503811480570254258903603224694465574129),(44490,23883094150264385550751501831181724667314104799878138247322161948146534199289),(44494,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44501,1)]⟩,⟨[(1782,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1826,1),(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224),(44494,1)],[(44500,4),(44501,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(1826,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (UserPathHash958C42.result++[(44494,1),(1782,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44500=(rho 1826)*(eval rho UserPathHash958C42.result+rho 44494-rho 1782) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 44500 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨259549,false,[(1826,1)],[(44494,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44502,1)],[(44503,1)],21764,[⟨[(1826,1),(44494,1)],[(44503,1)]⟩,⟨[(1826,1),(44494,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(44502,4),(44503,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(1826,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(44494,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 44502=(rho 1826)*(-rho 44494) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 44502 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(44470,5579934908212736977238010113730457006906792843192217773053283881663622591681),(44474,50978946942794420813356136484142315443152313428221265043903658432145007475423),(44478,51737743277955608982399432577620617083998176562860787771480331520415801857016),(44482,280754542936071555323583947036382301904172335755315562603417507239324752636),(44486,44773762128641970103070913747625047847186741019957383563700055475244115610384),(44490,28552781024861804928696238677004241170376447700649499575281496751792046985224),(44492,1),(44496,1)]
theorem child0_shape : canonical p child0=canonical p (UserPathHash958C42.result++[(44492,1),(44496,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(1781,1),(44492,52435875175126190479447740508185965837690552500527637822603658699938581184512),(44498,1)]
theorem child1_shape : canonical p child1=canonical p ([(1781,1),(44492,-1),(44498,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(1782,1),(44500,1)]
theorem child2_shape : canonical p child2=canonical p ([(1782,1),(44500,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(1783,1),(44502,1)]
theorem child3_shape : canonical p child3=canonical p ([(1783,1),(44502,1)]) := by decide +kernel
theorem inputs_shape : UserPathHash958C43.inputs=[[(0,5)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 1825=BooleanHints207.bitValue lo) (high : rho 1826=BooleanHints207.bitValue hi) :
    UserPathHash958C43.inputs.map (eval rho)=[(5:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho UserPathHash958C42.result) (rho 1781) (rho 1782) (rho 1783) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,5)]=(5:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (5:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho UserPathHash958C42.result) (rho 1781) (rho 1782) (rho 1783)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.UserPathSelector964RL04

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.leftSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.leftSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL04.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.leftSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL04.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.leftSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL04.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.rightSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.rightSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL04.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.rightSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL04.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.rightSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL04.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select0_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.select0_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select0_left
#print axioms ShielddSecurity.UserPathSelector964RL04.select0_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select0_right
#print axioms ShielddSecurity.UserPathSelector964RL04.select0_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select0_value
#print axioms ShielddSecurity.UserPathSelector964RL04.select0_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select1_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.select1_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select1_left
#print axioms ShielddSecurity.UserPathSelector964RL04.select1_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select1_right
#print axioms ShielddSecurity.UserPathSelector964RL04.select1_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select1_value
#print axioms ShielddSecurity.UserPathSelector964RL04.select1_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select2_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.select2_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select2_left
#print axioms ShielddSecurity.UserPathSelector964RL04.select2_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select2_right
#print axioms ShielddSecurity.UserPathSelector964RL04.select2_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select2_value
#print axioms ShielddSecurity.UserPathSelector964RL04.select2_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select3_checked
#print axioms ShielddSecurity.UserPathSelector964RL04.select3_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select3_left
#print axioms ShielddSecurity.UserPathSelector964RL04.select3_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select3_right
#print axioms ShielddSecurity.UserPathSelector964RL04.select3_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.select3_value
#print axioms ShielddSecurity.UserPathSelector964RL04.select3_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.child0_shape
#print axioms ShielddSecurity.UserPathSelector964RL04.child0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.child1_shape
#print axioms ShielddSecurity.UserPathSelector964RL04.child1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.child2_shape
#print axioms ShielddSecurity.UserPathSelector964RL04.child2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.child3_shape
#print axioms ShielddSecurity.UserPathSelector964RL04.child3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.inputs_shape
#print axioms ShielddSecurity.UserPathSelector964RL04.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL04.input_values
#print axioms ShielddSecurity.UserPathSelector964RL04.input_values
