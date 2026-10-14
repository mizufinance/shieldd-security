-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.VolumePathHash931C129
import ShielddSecurity.VolumePathHash931C130
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSelector945L05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨807031,false,[(8470,1)],[(8403,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(111450,1)],[(111451,1)],88712,[⟨[(8403,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8470,1),(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(111451,1)]⟩,⟨[(8403,1),(8470,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(111450,4),(111451,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(8470,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(8403,1)]++scaleLinear (-1) VolumePathHash931C129.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111450=(rho 8470)*(rho 8403-eval rho VolumePathHash931C129.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 111450 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨807034,false,[(8470,1)],[(8405,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(111452,1)],[(111453,1)],88714,[⟨[(8405,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8470,1),(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(111453,1)]⟩,⟨[(8405,1),(8470,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(111452,4),(111453,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(8470,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(8405,1)]++scaleLinear (-1) VolumePathHash931C129.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111452=(rho 8470)*(rho 8405-eval rho VolumePathHash931C129.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 111452 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨807043,false,[(8471,1)],[(8403,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289),(111450,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111454,1)],[(111455,1)],88716,[⟨[(8403,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8471,1),(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224),(111450,1)],[(111455,1)]⟩,⟨[(8403,1),(8471,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289),(111450,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111454,4),(111455,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(8471,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(8403,1),(111450,-1)]++scaleLinear (-1) VolumePathHash931C129.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111454=(rho 8471)*(rho 8403-rho 111450-eval rho VolumePathHash931C129.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 111454 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨807047,false,[(8471,1)],[(8403,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8404,1),(111450,1)],[(111456,1)],[(111457,1)],88718,[⟨[(8403,1),(8404,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8471,1),(111450,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111457,1)]⟩,⟨[(8403,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8404,1),(8471,1),(111450,1)],[(111456,4),(111457,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(8471,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(8404,1),(8403,-1),(111450,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111456=(rho 8471)*(rho 8404-rho 8403+rho 111450) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 111456 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨807051,false,[(8471,1)],[(8404,52435875175126190479447740508185965837690552500527637822603658699938581184512),(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224),(111452,1)],[(111458,1)],[(111459,1)],88720,[⟨[(8404,1),(8471,1),(111428,46855940266913453502209730394455508830783759657335420049550374818274958592832),(111432,1456928232331769666091604024043650394538239072306372778700000267793573709090),(111436,698131897170581497048307930565348753692375937666850051123327179522779327497),(111440,52155120632190118924124156561149583535786380164772322260000241192699256431877),(111444,7662113046484220376376826760560917990503811480570254258903603224694465574129),(111448,23883094150264385550751501831181724667314104799878138247322161948146534199289),(111452,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111459,1)]⟩,⟨[(8404,52435875175126190479447740508185965837690552500527637822603658699938581184512),(8471,1),(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224),(111452,1)],[(111458,4),(111459,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(8471,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (VolumePathHash931C129.result++[(111452,1),(8404,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111458=(rho 8471)*(eval rho VolumePathHash931C129.result+rho 111452-rho 8404) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 111458 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨807055,false,[(8471,1)],[(111452,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111460,1)],[(111461,1)],88722,[⟨[(8471,1),(111452,1)],[(111461,1)]⟩,⟨[(8471,1),(111452,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(111460,4),(111461,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(8471,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(111452,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 111460=(rho 8471)*(-rho 111452) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 111460 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(111428,5579934908212736977238010113730457006906792843192217773053283881663622591681),(111432,50978946942794420813356136484142315443152313428221265043903658432145007475423),(111436,51737743277955608982399432577620617083998176562860787771480331520415801857016),(111440,280754542936071555323583947036382301904172335755315562603417507239324752636),(111444,44773762128641970103070913747625047847186741019957383563700055475244115610384),(111448,28552781024861804928696238677004241170376447700649499575281496751792046985224),(111450,1),(111454,1)]
theorem child0_shape : canonical p child0=canonical p (VolumePathHash931C129.result++[(111450,1),(111454,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(8403,1),(111450,52435875175126190479447740508185965837690552500527637822603658699938581184512),(111456,1)]
theorem child1_shape : canonical p child1=canonical p ([(8403,1),(111450,-1),(111456,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(8404,1),(111458,1)]
theorem child2_shape : canonical p child2=canonical p ([(8404,1),(111458,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(8405,1),(111460,1)]
theorem child3_shape : canonical p child3=canonical p ([(8405,1),(111460,1)]) := by decide +kernel
theorem inputs_shape : VolumePathHash931C130.inputs=[[(0,6)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 8470=BooleanHints207.bitValue lo) (high : rho 8471=BooleanHints207.bitValue hi) :
    VolumePathHash931C130.inputs.map (eval rho)=[(6:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho VolumePathHash931C129.result) (rho 8403) (rho 8404) (rho 8405) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,6)]=(6:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (6:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho VolumePathHash931C129.result) (rho 8403) (rho 8404) (rho 8405)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.VolumePathSelector945L05

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.leftSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.leftSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L05.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.leftSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L05.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.leftSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L05.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.rightSwap_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.rightSwap_left
#print axioms ShielddSecurity.VolumePathSelector945L05.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.rightSwap_right
#print axioms ShielddSecurity.VolumePathSelector945L05.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.rightSwap_value
#print axioms ShielddSecurity.VolumePathSelector945L05.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select0_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.select0_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select0_left
#print axioms ShielddSecurity.VolumePathSelector945L05.select0_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select0_right
#print axioms ShielddSecurity.VolumePathSelector945L05.select0_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select0_value
#print axioms ShielddSecurity.VolumePathSelector945L05.select0_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select1_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.select1_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select1_left
#print axioms ShielddSecurity.VolumePathSelector945L05.select1_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select1_right
#print axioms ShielddSecurity.VolumePathSelector945L05.select1_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select1_value
#print axioms ShielddSecurity.VolumePathSelector945L05.select1_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select2_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.select2_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select2_left
#print axioms ShielddSecurity.VolumePathSelector945L05.select2_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select2_right
#print axioms ShielddSecurity.VolumePathSelector945L05.select2_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select2_value
#print axioms ShielddSecurity.VolumePathSelector945L05.select2_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select3_checked
#print axioms ShielddSecurity.VolumePathSelector945L05.select3_checked

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select3_left
#print axioms ShielddSecurity.VolumePathSelector945L05.select3_left

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select3_right
#print axioms ShielddSecurity.VolumePathSelector945L05.select3_right

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.select3_value
#print axioms ShielddSecurity.VolumePathSelector945L05.select3_value

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.child0_shape
#print axioms ShielddSecurity.VolumePathSelector945L05.child0_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.child1_shape
#print axioms ShielddSecurity.VolumePathSelector945L05.child1_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.child2_shape
#print axioms ShielddSecurity.VolumePathSelector945L05.child2_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.child3_shape
#print axioms ShielddSecurity.VolumePathSelector945L05.child3_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.inputs_shape
#print axioms ShielddSecurity.VolumePathSelector945L05.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.VolumePathSelector945L05.input_values
#print axioms ShielddSecurity.VolumePathSelector945L05.input_values
