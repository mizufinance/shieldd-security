-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathHash931C132
import ShielddSecurity.VolumePathHash931C133
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSelector945L08
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨823186,false,[(8476,1)],[(8412,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(112722,1)],[(112723,1)],89984,[⟨[(8412,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8476,1),(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(112723,1)]⟩,⟨[(8412,1),(8476,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(112722,4),(112723,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(8476,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(8412,1)]++scaleLinear (-1) VolumePathHash931C132.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112722=(rho 8476)*(rho 8412-eval rho VolumePathHash931C132.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 112722 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨823189,false,[(8476,1)],[(8414,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(112724,1)],[(112725,1)],89986,[⟨[(8414,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8476,1),(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(112725,1)]⟩,⟨[(8414,1),(8476,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(112724,4),(112725,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(8476,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(8414,1)]++scaleLinear (-1) VolumePathHash931C132.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112724=(rho 8476)*(rho 8414-eval rho VolumePathHash931C132.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 112724 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨823198,false,[(8477,1)],[(8412,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289),(112722,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112726,1)],[(112727,1)],89988,[⟨[(8412,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8477,1),(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224),(112722,1)],[(112727,1)]⟩,⟨[(8412,1),(8477,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289),(112722,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112726,4),(112727,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(8477,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(8412,1),(112722,-1)]++scaleLinear (-1) VolumePathHash931C132.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112726=(rho 8477)*(rho 8412-rho 112722-eval rho VolumePathHash931C132.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 112726 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨823202,false,[(8477,1)],[(8412,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8413,1),(112722,1)],[(112728,1)],[(112729,1)],89990,[⟨[(8412,1),(8413,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8477,1),(112722,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112729,1)]⟩,⟨[(8412,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8413,1),(8477,1),(112722,1)],[(112728,4),(112729,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(8477,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(8413,1),(8412,-1),(112722,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112728=(rho 8477)*(rho 8413-rho 8412+rho 112722) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 112728 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨823206,false,[(8477,1)],[(8413,52435875175126190479447740508185965837690552500527637822603658699938581184512),(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224),(112724,1)],[(112730,1)],[(112731,1)],89992,[⟨[(8413,1),(8477,1),(112700,46855940266913453502209730394455508830783759657335420049550374818274958592832),(112704,1456928232331769666091604024043650394538239072306372778700000267793573709090),(112708,698131897170581497048307930565348753692375937666850051123327179522779327497),(112712,52155120632190118924124156561149583535786380164772322260000241192699256431877),(112716,7662113046484220376376826760560917990503811480570254258903603224694465574129),(112720,23883094150264385550751501831181724667314104799878138247322161948146534199289),(112724,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112731,1)]⟩,⟨[(8413,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8477,1),(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224),(112724,1)],[(112730,4),(112731,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(8477,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (VolumePathHash931C132.result++[(112724,1),(8413,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112730=(rho 8477)*(eval rho VolumePathHash931C132.result+rho 112724-rho 8413) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 112730 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨823210,false,[(8477,1)],[(112724,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112732,1)],[(112733,1)],89994,[⟨[(8477,1),(112724,1)],[(112733,1)]⟩,⟨[(8477,1),(112724,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(112732,4),(112733,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(8477,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(112724,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 112732=(rho 8477)*(-rho 112724) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 112732 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(112700,5579934908212736977238010113730457006906792843192217773053283881663622591681),(112704,50978946942794420813356136484142315443152313428221265043903658432145007475423),(112708,51737743277955608982399432577620617083998176562860787771480331520415801857016),(112712,280754542936071555323583947036382301904172335755315562603417507239324752636),(112716,44773762128641970103070913747625047847186741019957383563700055475244115610384),(112720,28552781024861804928696238677004241170376447700649499575281496751792046985224),(112722,1),(112726,1)]
theorem child0_shape : canonical p child0=canonical p (VolumePathHash931C132.result++[(112722,1),(112726,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(8412,1),(112722,52435875175126190479447740508185965837690552500527637822603658699938581184512),(112728,1)]
theorem child1_shape : canonical p child1=canonical p ([(8412,1),(112722,-1),(112728,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(8413,1),(112730,1)]
theorem child2_shape : canonical p child2=canonical p ([(8413,1),(112730,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(8414,1),(112732,1)]
theorem child3_shape : canonical p child3=canonical p ([(8414,1),(112732,1)]) := by decide +kernel
theorem inputs_shape : VolumePathHash931C133.inputs=[[(0,9)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 8476=BooleanHints207.bitValue lo) (high : rho 8477=BooleanHints207.bitValue hi) :
    VolumePathHash931C133.inputs.map (eval rho)=[(9:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho VolumePathHash931C132.result) (rho 8412) (rho 8413) (rho 8414) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,9)]=(9:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (9:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho VolumePathHash931C132.result) (rho 8412) (rho 8413) (rho 8414)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.VolumePathSelector945L08

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.leftSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.leftSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L08.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.leftSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L08.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.leftSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L08.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.rightSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.rightSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L08.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.rightSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L08.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.rightSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L08.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select0_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.select0_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select0_left
#print axioms ShielddSecurity.VolumePathSelector945L08.select0_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select0_right
#print axioms ShielddSecurity.VolumePathSelector945L08.select0_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select0_value
#print axioms ShielddSecurity.VolumePathSelector945L08.select0_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select1_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.select1_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select1_left
#print axioms ShielddSecurity.VolumePathSelector945L08.select1_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select1_right
#print axioms ShielddSecurity.VolumePathSelector945L08.select1_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select1_value
#print axioms ShielddSecurity.VolumePathSelector945L08.select1_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select2_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.select2_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select2_left
#print axioms ShielddSecurity.VolumePathSelector945L08.select2_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select2_right
#print axioms ShielddSecurity.VolumePathSelector945L08.select2_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select2_value
#print axioms ShielddSecurity.VolumePathSelector945L08.select2_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select3_checked
#print axioms ShielddSecurity.VolumePathSelector945L08.select3_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select3_left
#print axioms ShielddSecurity.VolumePathSelector945L08.select3_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select3_right
#print axioms ShielddSecurity.VolumePathSelector945L08.select3_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.select3_value
#print axioms ShielddSecurity.VolumePathSelector945L08.select3_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.child0_shape
#print axioms ShielddSecurity.VolumePathSelector945L08.child0_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.child1_shape
#print axioms ShielddSecurity.VolumePathSelector945L08.child1_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.child2_shape
#print axioms ShielddSecurity.VolumePathSelector945L08.child2_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.child3_shape
#print axioms ShielddSecurity.VolumePathSelector945L08.child3_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.inputs_shape
#print axioms ShielddSecurity.VolumePathSelector945L08.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L08.input_values
#print axioms ShielddSecurity.VolumePathSelector945L08.input_values
