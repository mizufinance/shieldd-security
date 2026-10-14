-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathHash931C144
import ShielddSecurity.VolumePathHash931C145
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSelector945L20
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨887806,false,[(8500,1)],[(8448,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(117810,1)],[(117811,1)],95072,[⟨[(8448,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8500,1),(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(117811,1)]⟩,⟨[(8448,1),(8500,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(117810,4),(117811,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(8500,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(8448,1)]++scaleLinear (-1) VolumePathHash931C144.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117810=(rho 8500)*(rho 8448-eval rho VolumePathHash931C144.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 117810 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨887809,false,[(8500,1)],[(8450,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(117812,1)],[(117813,1)],95074,[⟨[(8450,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8500,1),(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(117813,1)]⟩,⟨[(8450,1),(8500,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(117812,4),(117813,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(8500,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(8450,1)]++scaleLinear (-1) VolumePathHash931C144.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117812=(rho 8500)*(rho 8450-eval rho VolumePathHash931C144.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 117812 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨887818,false,[(8501,1)],[(8448,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289),(117810,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117814,1)],[(117815,1)],95076,[⟨[(8448,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8501,1),(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224),(117810,1)],[(117815,1)]⟩,⟨[(8448,1),(8501,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289),(117810,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117814,4),(117815,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(8501,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(8448,1),(117810,-1)]++scaleLinear (-1) VolumePathHash931C144.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117814=(rho 8501)*(rho 8448-rho 117810-eval rho VolumePathHash931C144.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 117814 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨887822,false,[(8501,1)],[(8448,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8449,1),(117810,1)],[(117816,1)],[(117817,1)],95078,[⟨[(8448,1),(8449,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8501,1),(117810,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117817,1)]⟩,⟨[(8448,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8449,1),(8501,1),(117810,1)],[(117816,4),(117817,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(8501,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(8449,1),(8448,-1),(117810,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117816=(rho 8501)*(rho 8449-rho 8448+rho 117810) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 117816 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨887826,false,[(8501,1)],[(8449,52435875175126190479447740508185965837690552500527637822603658699938581184512),(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224),(117812,1)],[(117818,1)],[(117819,1)],95080,[⟨[(8449,1),(8501,1),(117788,46855940266913453502209730394455508830783759657335420049550374818274958592832),(117792,1456928232331769666091604024043650394538239072306372778700000267793573709090),(117796,698131897170581497048307930565348753692375937666850051123327179522779327497),(117800,52155120632190118924124156561149583535786380164772322260000241192699256431877),(117804,7662113046484220376376826760560917990503811480570254258903603224694465574129),(117808,23883094150264385550751501831181724667314104799878138247322161948146534199289),(117812,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117819,1)]⟩,⟨[(8449,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8501,1),(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224),(117812,1)],[(117818,4),(117819,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(8501,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (VolumePathHash931C144.result++[(117812,1),(8449,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117818=(rho 8501)*(eval rho VolumePathHash931C144.result+rho 117812-rho 8449) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 117818 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨887830,false,[(8501,1)],[(117812,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117820,1)],[(117821,1)],95082,[⟨[(8501,1),(117812,1)],[(117821,1)]⟩,⟨[(8501,1),(117812,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(117820,4),(117821,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(8501,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(117812,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 117820=(rho 8501)*(-rho 117812) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 117820 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(117788,5579934908212736977238010113730457006906792843192217773053283881663622591681),(117792,50978946942794420813356136484142315443152313428221265043903658432145007475423),(117796,51737743277955608982399432577620617083998176562860787771480331520415801857016),(117800,280754542936071555323583947036382301904172335755315562603417507239324752636),(117804,44773762128641970103070913747625047847186741019957383563700055475244115610384),(117808,28552781024861804928696238677004241170376447700649499575281496751792046985224),(117810,1),(117814,1)]
theorem child0_shape : canonical p child0=canonical p (VolumePathHash931C144.result++[(117810,1),(117814,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(8448,1),(117810,52435875175126190479447740508185965837690552500527637822603658699938581184512),(117816,1)]
theorem child1_shape : canonical p child1=canonical p ([(8448,1),(117810,-1),(117816,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(8449,1),(117818,1)]
theorem child2_shape : canonical p child2=canonical p ([(8449,1),(117818,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(8450,1),(117820,1)]
theorem child3_shape : canonical p child3=canonical p ([(8450,1),(117820,1)]) := by decide +kernel
theorem inputs_shape : VolumePathHash931C145.inputs=[[(0,21)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 8500=BooleanHints207.bitValue lo) (high : rho 8501=BooleanHints207.bitValue hi) :
    VolumePathHash931C145.inputs.map (eval rho)=[(21:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho VolumePathHash931C144.result) (rho 8448) (rho 8449) (rho 8450) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,21)]=(21:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (21:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho VolumePathHash931C144.result) (rho 8448) (rho 8449) (rho 8450)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.VolumePathSelector945L20

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.leftSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.leftSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L20.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.leftSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L20.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.leftSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L20.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.rightSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.rightSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L20.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.rightSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L20.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.rightSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L20.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select0_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.select0_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select0_left
#print axioms ShielddSecurity.VolumePathSelector945L20.select0_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select0_right
#print axioms ShielddSecurity.VolumePathSelector945L20.select0_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select0_value
#print axioms ShielddSecurity.VolumePathSelector945L20.select0_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select1_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.select1_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select1_left
#print axioms ShielddSecurity.VolumePathSelector945L20.select1_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select1_right
#print axioms ShielddSecurity.VolumePathSelector945L20.select1_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select1_value
#print axioms ShielddSecurity.VolumePathSelector945L20.select1_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select2_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.select2_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select2_left
#print axioms ShielddSecurity.VolumePathSelector945L20.select2_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select2_right
#print axioms ShielddSecurity.VolumePathSelector945L20.select2_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select2_value
#print axioms ShielddSecurity.VolumePathSelector945L20.select2_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select3_checked
#print axioms ShielddSecurity.VolumePathSelector945L20.select3_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select3_left
#print axioms ShielddSecurity.VolumePathSelector945L20.select3_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select3_right
#print axioms ShielddSecurity.VolumePathSelector945L20.select3_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.select3_value
#print axioms ShielddSecurity.VolumePathSelector945L20.select3_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.child0_shape
#print axioms ShielddSecurity.VolumePathSelector945L20.child0_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.child1_shape
#print axioms ShielddSecurity.VolumePathSelector945L20.child1_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.child2_shape
#print axioms ShielddSecurity.VolumePathSelector945L20.child2_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.child3_shape
#print axioms ShielddSecurity.VolumePathSelector945L20.child3_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.inputs_shape
#print axioms ShielddSecurity.VolumePathSelector945L20.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L20.input_values
#print axioms ShielddSecurity.VolumePathSelector945L20.input_values
