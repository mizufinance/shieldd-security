-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.UserPathHash958C50
import ShielddSecurity.UserPathHash958C51
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSelector964RL12
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨302605,false,[(1841,1)],[(1805,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(47884,1)],[(47885,1)],25146,[⟨[(1805,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1841,1),(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(47885,1)]⟩,⟨[(1805,1),(1841,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(47884,4),(47885,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(1841,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(1805,1)]++scaleLinear (-1) UserPathHash958C50.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47884=(rho 1841)*(rho 1805-eval rho UserPathHash958C50.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 47884 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨302608,false,[(1841,1)],[(1807,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(47886,1)],[(47887,1)],25148,[⟨[(1807,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1841,1),(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(47887,1)]⟩,⟨[(1807,1),(1841,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(47886,4),(47887,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(1841,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(1807,1)]++scaleLinear (-1) UserPathHash958C50.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47886=(rho 1841)*(rho 1807-eval rho UserPathHash958C50.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 47886 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨302617,false,[(1842,1)],[(1805,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289),(47884,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47888,1)],[(47889,1)],25150,[⟨[(1805,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1842,1),(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224),(47884,1)],[(47889,1)]⟩,⟨[(1805,1),(1842,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289),(47884,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47888,4),(47889,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(1842,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(1805,1),(47884,-1)]++scaleLinear (-1) UserPathHash958C50.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47888=(rho 1842)*(rho 1805-rho 47884-eval rho UserPathHash958C50.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 47888 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨302621,false,[(1842,1)],[(1805,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1806,1),(47884,1)],[(47890,1)],[(47891,1)],25152,[⟨[(1805,1),(1806,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1842,1),(47884,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47891,1)]⟩,⟨[(1805,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1806,1),(1842,1),(47884,1)],[(47890,4),(47891,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(1842,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(1806,1),(1805,-1),(47884,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47890=(rho 1842)*(rho 1806-rho 1805+rho 47884) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 47890 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨302625,false,[(1842,1)],[(1806,52435875175126190479447740508185965837690552500527637822603658699938581184512),(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224),(47886,1)],[(47892,1)],[(47893,1)],25154,[⟨[(1806,1),(1842,1),(47862,46855940266913453502209730394455508830783759657335420049550374818274958592832),(47866,1456928232331769666091604024043650394538239072306372778700000267793573709090),(47870,698131897170581497048307930565348753692375937666850051123327179522779327497),(47874,52155120632190118924124156561149583535786380164772322260000241192699256431877),(47878,7662113046484220376376826760560917990503811480570254258903603224694465574129),(47882,23883094150264385550751501831181724667314104799878138247322161948146534199289),(47886,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47893,1)]⟩,⟨[(1806,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1842,1),(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224),(47886,1)],[(47892,4),(47893,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(1842,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (UserPathHash958C50.result++[(47886,1),(1806,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47892=(rho 1842)*(eval rho UserPathHash958C50.result+rho 47886-rho 1806) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 47892 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨302629,false,[(1842,1)],[(47886,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47894,1)],[(47895,1)],25156,[⟨[(1842,1),(47886,1)],[(47895,1)]⟩,⟨[(1842,1),(47886,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(47894,4),(47895,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(1842,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(47886,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 47894=(rho 1842)*(-rho 47886) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 47894 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(47862,5579934908212736977238010113730457006906792843192217773053283881663622591681),(47866,50978946942794420813356136484142315443152313428221265043903658432145007475423),(47870,51737743277955608982399432577620617083998176562860787771480331520415801857016),(47874,280754542936071555323583947036382301904172335755315562603417507239324752636),(47878,44773762128641970103070913747625047847186741019957383563700055475244115610384),(47882,28552781024861804928696238677004241170376447700649499575281496751792046985224),(47884,1),(47888,1)]
theorem child0_shape : canonical p child0=canonical p (UserPathHash958C50.result++[(47884,1),(47888,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(1805,1),(47884,52435875175126190479447740508185965837690552500527637822603658699938581184512),(47890,1)]
theorem child1_shape : canonical p child1=canonical p ([(1805,1),(47884,-1),(47890,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(1806,1),(47892,1)]
theorem child2_shape : canonical p child2=canonical p ([(1806,1),(47892,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(1807,1),(47894,1)]
theorem child3_shape : canonical p child3=canonical p ([(1807,1),(47894,1)]) := by decide +kernel
theorem inputs_shape : UserPathHash958C51.inputs=[[(0,13)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 1841=BooleanHints207.bitValue lo) (high : rho 1842=BooleanHints207.bitValue hi) :
    UserPathHash958C51.inputs.map (eval rho)=[(13:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho UserPathHash958C50.result) (rho 1805) (rho 1806) (rho 1807) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,13)]=(13:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (13:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho UserPathHash958C50.result) (rho 1805) (rho 1806) (rho 1807)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.UserPathSelector964RL12

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.leftSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.leftSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL12.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.leftSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL12.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.leftSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL12.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.rightSwap_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.rightSwap_left
#print axioms ShielddSecurity.UserPathSelector964RL12.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.rightSwap_right
#print axioms ShielddSecurity.UserPathSelector964RL12.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.rightSwap_value
#print axioms ShielddSecurity.UserPathSelector964RL12.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select0_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.select0_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select0_left
#print axioms ShielddSecurity.UserPathSelector964RL12.select0_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select0_right
#print axioms ShielddSecurity.UserPathSelector964RL12.select0_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select0_value
#print axioms ShielddSecurity.UserPathSelector964RL12.select0_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select1_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.select1_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select1_left
#print axioms ShielddSecurity.UserPathSelector964RL12.select1_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select1_right
#print axioms ShielddSecurity.UserPathSelector964RL12.select1_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select1_value
#print axioms ShielddSecurity.UserPathSelector964RL12.select1_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select2_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.select2_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select2_left
#print axioms ShielddSecurity.UserPathSelector964RL12.select2_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select2_right
#print axioms ShielddSecurity.UserPathSelector964RL12.select2_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select2_value
#print axioms ShielddSecurity.UserPathSelector964RL12.select2_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select3_checked
#print axioms ShielddSecurity.UserPathSelector964RL12.select3_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select3_left
#print axioms ShielddSecurity.UserPathSelector964RL12.select3_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select3_right
#print axioms ShielddSecurity.UserPathSelector964RL12.select3_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.select3_value
#print axioms ShielddSecurity.UserPathSelector964RL12.select3_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.child0_shape
#print axioms ShielddSecurity.UserPathSelector964RL12.child0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.child1_shape
#print axioms ShielddSecurity.UserPathSelector964RL12.child1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.child2_shape
#print axioms ShielddSecurity.UserPathSelector964RL12.child2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.child3_shape
#print axioms ShielddSecurity.UserPathSelector964RL12.child3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.inputs_shape
#print axioms ShielddSecurity.UserPathSelector964RL12.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964RL12.input_values
#print axioms ShielddSecurity.UserPathSelector964RL12.input_values
