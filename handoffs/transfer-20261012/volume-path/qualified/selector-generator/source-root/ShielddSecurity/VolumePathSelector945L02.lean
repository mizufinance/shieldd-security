-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathHash931C126
import ShielddSecurity.VolumePathHash931C127
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSelector945L02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨790876,false,[(8464,1)],[(8394,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(110178,1)],[(110179,1)],87440,[⟨[(8394,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8464,1),(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(110179,1)]⟩,⟨[(8394,1),(8464,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(110178,4),(110179,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(8464,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(8394,1)]++scaleLinear (-1) VolumePathHash931C126.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110178=(rho 8464)*(rho 8394-eval rho VolumePathHash931C126.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 110178 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨790879,false,[(8464,1)],[(8396,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(110180,1)],[(110181,1)],87442,[⟨[(8396,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8464,1),(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(110181,1)]⟩,⟨[(8396,1),(8464,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(110180,4),(110181,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(8464,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(8396,1)]++scaleLinear (-1) VolumePathHash931C126.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110180=(rho 8464)*(rho 8396-eval rho VolumePathHash931C126.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 110180 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨790888,false,[(8465,1)],[(8394,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289),(110178,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110182,1)],[(110183,1)],87444,[⟨[(8394,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8465,1),(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224),(110178,1)],[(110183,1)]⟩,⟨[(8394,1),(8465,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289),(110178,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110182,4),(110183,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(8465,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(8394,1),(110178,-1)]++scaleLinear (-1) VolumePathHash931C126.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110182=(rho 8465)*(rho 8394-rho 110178-eval rho VolumePathHash931C126.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 110182 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨790892,false,[(8465,1)],[(8394,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8395,1),(110178,1)],[(110184,1)],[(110185,1)],87446,[⟨[(8394,1),(8395,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8465,1),(110178,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110185,1)]⟩,⟨[(8394,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8395,1),(8465,1),(110178,1)],[(110184,4),(110185,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(8465,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(8395,1),(8394,-1),(110178,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110184=(rho 8465)*(rho 8395-rho 8394+rho 110178) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 110184 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨790896,false,[(8465,1)],[(8395,52435875175126190479447740508185965837690552500527637822603658699938581184512),(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224),(110180,1)],[(110186,1)],[(110187,1)],87448,[⟨[(8395,1),(8465,1),(110156,46855940266913453502209730394455508830783759657335420049550374818274958592832),(110160,1456928232331769666091604024043650394538239072306372778700000267793573709090),(110164,698131897170581497048307930565348753692375937666850051123327179522779327497),(110168,52155120632190118924124156561149583535786380164772322260000241192699256431877),(110172,7662113046484220376376826760560917990503811480570254258903603224694465574129),(110176,23883094150264385550751501831181724667314104799878138247322161948146534199289),(110180,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110187,1)]⟩,⟨[(8395,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8465,1),(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224),(110180,1)],[(110186,4),(110187,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(8465,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (VolumePathHash931C126.result++[(110180,1),(8395,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110186=(rho 8465)*(eval rho VolumePathHash931C126.result+rho 110180-rho 8395) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 110186 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨790900,false,[(8465,1)],[(110180,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110188,1)],[(110189,1)],87450,[⟨[(8465,1),(110180,1)],[(110189,1)]⟩,⟨[(8465,1),(110180,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(110188,4),(110189,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(8465,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(110180,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 110188=(rho 8465)*(-rho 110180) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 110188 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(110156,5579934908212736977238010113730457006906792843192217773053283881663622591681),(110160,50978946942794420813356136484142315443152313428221265043903658432145007475423),(110164,51737743277955608982399432577620617083998176562860787771480331520415801857016),(110168,280754542936071555323583947036382301904172335755315562603417507239324752636),(110172,44773762128641970103070913747625047847186741019957383563700055475244115610384),(110176,28552781024861804928696238677004241170376447700649499575281496751792046985224),(110178,1),(110182,1)]
theorem child0_shape : canonical p child0=canonical p (VolumePathHash931C126.result++[(110178,1),(110182,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(8394,1),(110178,52435875175126190479447740508185965837690552500527637822603658699938581184512),(110184,1)]
theorem child1_shape : canonical p child1=canonical p ([(8394,1),(110178,-1),(110184,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(8395,1),(110186,1)]
theorem child2_shape : canonical p child2=canonical p ([(8395,1),(110186,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(8396,1),(110188,1)]
theorem child3_shape : canonical p child3=canonical p ([(8396,1),(110188,1)]) := by decide +kernel
theorem inputs_shape : VolumePathHash931C127.inputs=[[(0,3)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 8464=BooleanHints207.bitValue lo) (high : rho 8465=BooleanHints207.bitValue hi) :
    VolumePathHash931C127.inputs.map (eval rho)=[(3:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho VolumePathHash931C126.result) (rho 8394) (rho 8395) (rho 8396) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,3)]=(3:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (3:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho VolumePathHash931C126.result) (rho 8394) (rho 8395) (rho 8396)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.VolumePathSelector945L02

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.leftSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.leftSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L02.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.leftSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L02.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.leftSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L02.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.rightSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.rightSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L02.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.rightSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L02.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.rightSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L02.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select0_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.select0_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select0_left
#print axioms ShielddSecurity.VolumePathSelector945L02.select0_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select0_right
#print axioms ShielddSecurity.VolumePathSelector945L02.select0_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select0_value
#print axioms ShielddSecurity.VolumePathSelector945L02.select0_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select1_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.select1_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select1_left
#print axioms ShielddSecurity.VolumePathSelector945L02.select1_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select1_right
#print axioms ShielddSecurity.VolumePathSelector945L02.select1_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select1_value
#print axioms ShielddSecurity.VolumePathSelector945L02.select1_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select2_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.select2_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select2_left
#print axioms ShielddSecurity.VolumePathSelector945L02.select2_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select2_right
#print axioms ShielddSecurity.VolumePathSelector945L02.select2_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select2_value
#print axioms ShielddSecurity.VolumePathSelector945L02.select2_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select3_checked
#print axioms ShielddSecurity.VolumePathSelector945L02.select3_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select3_left
#print axioms ShielddSecurity.VolumePathSelector945L02.select3_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select3_right
#print axioms ShielddSecurity.VolumePathSelector945L02.select3_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.select3_value
#print axioms ShielddSecurity.VolumePathSelector945L02.select3_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.child0_shape
#print axioms ShielddSecurity.VolumePathSelector945L02.child0_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.child1_shape
#print axioms ShielddSecurity.VolumePathSelector945L02.child1_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.child2_shape
#print axioms ShielddSecurity.VolumePathSelector945L02.child2_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.child3_shape
#print axioms ShielddSecurity.VolumePathSelector945L02.child3_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.inputs_shape
#print axioms ShielddSecurity.VolumePathSelector945L02.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L02.input_values
#print axioms ShielddSecurity.VolumePathSelector945L02.input_values
