-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathHash931C125
import ShielddSecurity.VolumePathHash931C126
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSelector945L01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨785491,false,[(8462,1)],[(8391,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(109754,1)],[(109755,1)],87016,[⟨[(8391,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8462,1),(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(109755,1)]⟩,⟨[(8391,1),(8462,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(109754,4),(109755,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(8462,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(8391,1)]++scaleLinear (-1) VolumePathHash931C125.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109754=(rho 8462)*(rho 8391-eval rho VolumePathHash931C125.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 109754 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨785494,false,[(8462,1)],[(8393,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(109756,1)],[(109757,1)],87018,[⟨[(8393,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8462,1),(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(109757,1)]⟩,⟨[(8393,1),(8462,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(109756,4),(109757,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(8462,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(8393,1)]++scaleLinear (-1) VolumePathHash931C125.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109756=(rho 8462)*(rho 8393-eval rho VolumePathHash931C125.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 109756 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨785503,false,[(8463,1)],[(8391,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289),(109754,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109758,1)],[(109759,1)],87020,[⟨[(8391,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8463,1),(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224),(109754,1)],[(109759,1)]⟩,⟨[(8391,1),(8463,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289),(109754,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109758,4),(109759,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(8463,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(8391,1),(109754,-1)]++scaleLinear (-1) VolumePathHash931C125.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109758=(rho 8463)*(rho 8391-rho 109754-eval rho VolumePathHash931C125.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 109758 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨785507,false,[(8463,1)],[(8391,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8392,1),(109754,1)],[(109760,1)],[(109761,1)],87022,[⟨[(8391,1),(8392,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8463,1),(109754,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109761,1)]⟩,⟨[(8391,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8392,1),(8463,1),(109754,1)],[(109760,4),(109761,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(8463,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(8392,1),(8391,-1),(109754,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109760=(rho 8463)*(rho 8392-rho 8391+rho 109754) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 109760 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨785511,false,[(8463,1)],[(8392,52435875175126190479447740508185965837690552500527637822603658699938581184512),(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224),(109756,1)],[(109762,1)],[(109763,1)],87024,[⟨[(8392,1),(8463,1),(109732,46855940266913453502209730394455508830783759657335420049550374818274958592832),(109736,1456928232331769666091604024043650394538239072306372778700000267793573709090),(109740,698131897170581497048307930565348753692375937666850051123327179522779327497),(109744,52155120632190118924124156561149583535786380164772322260000241192699256431877),(109748,7662113046484220376376826760560917990503811480570254258903603224694465574129),(109752,23883094150264385550751501831181724667314104799878138247322161948146534199289),(109756,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109763,1)]⟩,⟨[(8392,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8463,1),(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224),(109756,1)],[(109762,4),(109763,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(8463,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (VolumePathHash931C125.result++[(109756,1),(8392,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109762=(rho 8463)*(eval rho VolumePathHash931C125.result+rho 109756-rho 8392) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 109762 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨785515,false,[(8463,1)],[(109756,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109764,1)],[(109765,1)],87026,[⟨[(8463,1),(109756,1)],[(109765,1)]⟩,⟨[(8463,1),(109756,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(109764,4),(109765,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(8463,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(109756,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 109764=(rho 8463)*(-rho 109756) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 109764 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(109732,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109736,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109740,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109744,280754542936071555323583947036382301904172335755315562603417507239324752636),(109748,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109752,28552781024861804928696238677004241170376447700649499575281496751792046985224),(109754,1),(109758,1)]
theorem child0_shape : canonical p child0=canonical p (VolumePathHash931C125.result++[(109754,1),(109758,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(8391,1),(109754,52435875175126190479447740508185965837690552500527637822603658699938581184512),(109760,1)]
theorem child1_shape : canonical p child1=canonical p ([(8391,1),(109754,-1),(109760,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(8392,1),(109762,1)]
theorem child2_shape : canonical p child2=canonical p ([(8392,1),(109762,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(8393,1),(109764,1)]
theorem child3_shape : canonical p child3=canonical p ([(8393,1),(109764,1)]) := by decide +kernel
theorem inputs_shape : VolumePathHash931C126.inputs=[[(0,2)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 8462=BooleanHints207.bitValue lo) (high : rho 8463=BooleanHints207.bitValue hi) :
    VolumePathHash931C126.inputs.map (eval rho)=[(2:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho VolumePathHash931C125.result) (rho 8391) (rho 8392) (rho 8393) := by
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
  have selected := QuaternarySelector944.select lo hi (eval rho VolumePathHash931C125.result) (rho 8391) (rho 8392) (rho 8393)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.VolumePathSelector945L01

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.leftSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.leftSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L01.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.leftSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L01.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.leftSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L01.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.rightSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.rightSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L01.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.rightSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L01.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.rightSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L01.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select0_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.select0_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select0_left
#print axioms ShielddSecurity.VolumePathSelector945L01.select0_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select0_right
#print axioms ShielddSecurity.VolumePathSelector945L01.select0_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select0_value
#print axioms ShielddSecurity.VolumePathSelector945L01.select0_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select1_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.select1_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select1_left
#print axioms ShielddSecurity.VolumePathSelector945L01.select1_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select1_right
#print axioms ShielddSecurity.VolumePathSelector945L01.select1_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select1_value
#print axioms ShielddSecurity.VolumePathSelector945L01.select1_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select2_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.select2_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select2_left
#print axioms ShielddSecurity.VolumePathSelector945L01.select2_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select2_right
#print axioms ShielddSecurity.VolumePathSelector945L01.select2_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select2_value
#print axioms ShielddSecurity.VolumePathSelector945L01.select2_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select3_checked
#print axioms ShielddSecurity.VolumePathSelector945L01.select3_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select3_left
#print axioms ShielddSecurity.VolumePathSelector945L01.select3_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select3_right
#print axioms ShielddSecurity.VolumePathSelector945L01.select3_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.select3_value
#print axioms ShielddSecurity.VolumePathSelector945L01.select3_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.child0_shape
#print axioms ShielddSecurity.VolumePathSelector945L01.child0_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.child1_shape
#print axioms ShielddSecurity.VolumePathSelector945L01.child1_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.child2_shape
#print axioms ShielddSecurity.VolumePathSelector945L01.child2_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.child3_shape
#print axioms ShielddSecurity.VolumePathSelector945L01.child3_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.inputs_shape
#print axioms ShielddSecurity.VolumePathSelector945L01.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L01.input_values
#print axioms ShielddSecurity.VolumePathSelector945L01.input_values
