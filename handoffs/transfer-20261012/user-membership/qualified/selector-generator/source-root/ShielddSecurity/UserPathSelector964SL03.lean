-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.UserPathHash958C24
import ShielddSecurity.UserPathHash958C25
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSelector964SL03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
noncomputable def leftSwapEntry : Entry := ⟨156414,false,[(1585,1)],[(1540,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(36114,1)],[(36115,1)],13376,[⟨[(1540,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1585,1),(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(36115,1)]⟩,⟨[(1540,1),(1585,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(36114,4),(36115,1)]⟩]⟩
theorem leftSwap_checked : check leftSwapEntry=true := by decide +kernel
theorem leftSwap_left : canonical p leftSwapEntry.left=canonical p ([(1585,1)]) := by decide +kernel
theorem leftSwap_right : canonical p leftSwapEntry.right=canonical p ([(1540,1)]++scaleLinear (-1) UserPathHash958C24.result) := by decide +kernel
theorem leftSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36114=(rho 1585)*(rho 1540-eval rho UserPathHash958C24.result) := by
  have result := MapArithmeticAdapter704.equation leftSwapEntry leftSwap_checked rho arithmetic
  have output : eval rho leftSwapEntry.output=rho 36114 := by simp [leftSwapEntry,eval]
  have square : leftSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ leftSwap_left,canonical_equal rho _ _ leftSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def rightSwapEntry : Entry := ⟨156417,false,[(1585,1)],[(1542,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(36116,1)],[(36117,1)],13378,[⟨[(1542,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1585,1),(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(36117,1)]⟩,⟨[(1542,1),(1585,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289)],[(36116,4),(36117,1)]⟩]⟩
theorem rightSwap_checked : check rightSwapEntry=true := by decide +kernel
theorem rightSwap_left : canonical p rightSwapEntry.left=canonical p ([(1585,1)]) := by decide +kernel
theorem rightSwap_right : canonical p rightSwapEntry.right=canonical p ([(1542,1)]++scaleLinear (-1) UserPathHash958C24.result) := by decide +kernel
theorem rightSwap_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36116=(rho 1585)*(rho 1542-eval rho UserPathHash958C24.result) := by
  have result := MapArithmeticAdapter704.equation rightSwapEntry rightSwap_checked rho arithmetic
  have output : eval rho rightSwapEntry.output=rho 36116 := by simp [rightSwapEntry,eval]
  have square : rightSwapEntry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ rightSwap_left,canonical_equal rho _ _ rightSwap_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select0Entry : Entry := ⟨156426,false,[(1586,1)],[(1540,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289),(36114,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36118,1)],[(36119,1)],13380,[⟨[(1540,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1586,1),(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224),(36114,1)],[(36119,1)]⟩,⟨[(1540,1),(1586,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289),(36114,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36118,4),(36119,1)]⟩]⟩
theorem select0_checked : check select0Entry=true := by decide +kernel
theorem select0_left : canonical p select0Entry.left=canonical p ([(1586,1)]) := by decide +kernel
theorem select0_right : canonical p select0Entry.right=canonical p ([(1540,1),(36114,-1)]++scaleLinear (-1) UserPathHash958C24.result) := by decide +kernel
theorem select0_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36118=(rho 1586)*(rho 1540-rho 36114-eval rho UserPathHash958C24.result) := by
  have result := MapArithmeticAdapter704.equation select0Entry select0_checked rho arithmetic
  have output : eval rho select0Entry.output=rho 36118 := by simp [select0Entry,eval]
  have square : select0Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select0_left,canonical_equal rho _ _ select0_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select1Entry : Entry := ⟨156430,false,[(1586,1)],[(1540,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1541,1),(36114,1)],[(36120,1)],[(36121,1)],13382,[⟨[(1540,1),(1541,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1586,1),(36114,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36121,1)]⟩,⟨[(1540,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1541,1),(1586,1),(36114,1)],[(36120,4),(36121,1)]⟩]⟩
theorem select1_checked : check select1Entry=true := by decide +kernel
theorem select1_left : canonical p select1Entry.left=canonical p ([(1586,1)]) := by decide +kernel
theorem select1_right : canonical p select1Entry.right=canonical p ([(1541,1),(1540,-1),(36114,1)]) := by decide +kernel
theorem select1_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36120=(rho 1586)*(rho 1541-rho 1540+rho 36114) := by
  have result := MapArithmeticAdapter704.equation select1Entry select1_checked rho arithmetic
  have output : eval rho select1Entry.output=rho 36120 := by simp [select1Entry,eval]
  have square : select1Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select1_left,canonical_equal rho _ _ select1_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select2Entry : Entry := ⟨156434,false,[(1586,1)],[(1541,52435875175126190479447740508185965837690552500527637822603658699938581184512),(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224),(36116,1)],[(36122,1)],[(36123,1)],13384,[⟨[(1541,1),(1586,1),(36092,46855940266913453502209730394455508830783759657335420049550374818274958592832),(36096,1456928232331769666091604024043650394538239072306372778700000267793573709090),(36100,698131897170581497048307930565348753692375937666850051123327179522779327497),(36104,52155120632190118924124156561149583535786380164772322260000241192699256431877),(36108,7662113046484220376376826760560917990503811480570254258903603224694465574129),(36112,23883094150264385550751501831181724667314104799878138247322161948146534199289),(36116,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36123,1)]⟩,⟨[(1541,52435875175126190479447740508185965837690552500527637822603658699938581184512),(1586,1),(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224),(36116,1)],[(36122,4),(36123,1)]⟩]⟩
theorem select2_checked : check select2Entry=true := by decide +kernel
theorem select2_left : canonical p select2Entry.left=canonical p ([(1586,1)]) := by decide +kernel
theorem select2_right : canonical p select2Entry.right=canonical p (UserPathHash958C24.result++[(36116,1),(1541,-1)]) := by decide +kernel
theorem select2_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36122=(rho 1586)*(eval rho UserPathHash958C24.result+rho 36116-rho 1541) := by
  have result := MapArithmeticAdapter704.equation select2Entry select2_checked rho arithmetic
  have output : eval rho select2Entry.output=rho 36122 := by simp [select2Entry,eval]
  have square : select2Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select2_left,canonical_equal rho _ _ select2_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def select3Entry : Entry := ⟨156438,false,[(1586,1)],[(36116,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36124,1)],[(36125,1)],13386,[⟨[(1586,1),(36116,1)],[(36125,1)]⟩,⟨[(1586,1),(36116,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(36124,4),(36125,1)]⟩]⟩
theorem select3_checked : check select3Entry=true := by decide +kernel
theorem select3_left : canonical p select3Entry.left=canonical p ([(1586,1)]) := by decide +kernel
theorem select3_right : canonical p select3Entry.right=canonical p ([(36116,-1)]) := by decide +kernel
theorem select3_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 36124=(rho 1586)*(-rho 36116) := by
  have result := MapArithmeticAdapter704.equation select3Entry select3_checked rho arithmetic
  have output : eval rho select3Entry.output=rho 36124 := by simp [select3Entry,eval]
  have square : select3Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ select3_left,canonical_equal rho _ _ select3_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
noncomputable def child0 : Linear := [(36092,5579934908212736977238010113730457006906792843192217773053283881663622591681),(36096,50978946942794420813356136484142315443152313428221265043903658432145007475423),(36100,51737743277955608982399432577620617083998176562860787771480331520415801857016),(36104,280754542936071555323583947036382301904172335755315562603417507239324752636),(36108,44773762128641970103070913747625047847186741019957383563700055475244115610384),(36112,28552781024861804928696238677004241170376447700649499575281496751792046985224),(36114,1),(36118,1)]
theorem child0_shape : canonical p child0=canonical p (UserPathHash958C24.result++[(36114,1),(36118,1)]) := by decide +kernel
noncomputable def child1 : Linear := [(1540,1),(36114,52435875175126190479447740508185965837690552500527637822603658699938581184512),(36120,1)]
theorem child1_shape : canonical p child1=canonical p ([(1540,1),(36114,-1),(36120,1)]) := by decide +kernel
noncomputable def child2 : Linear := [(1541,1),(36122,1)]
theorem child2_shape : canonical p child2=canonical p ([(1541,1),(36122,1)]) := by decide +kernel
noncomputable def child3 : Linear := [(1542,1),(36124,1)]
theorem child3_shape : canonical p child3=canonical p ([(1542,1),(36124,1)]) := by decide +kernel
theorem inputs_shape : UserPathHash958C25.inputs=[[(0,4)],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho 1585=BooleanHints207.bitValue lo) (high : rho 1586=BooleanHints207.bitValue hi) :
    UserPathHash958C25.inputs.map (eval rho)=[(4:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) (eval rho UserPathHash958C24.result) (rho 1540) (rho 1541) (rho 1542) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,4)]=(4:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => (4:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi (eval rho UserPathHash958C24.result) (rho 1540) (rho 1541) (rho 1542)
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.UserPathSelector964SL03

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.leftSwap_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.leftSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.leftSwap_left
#print axioms ShielddSecurity.UserPathSelector964SL03.leftSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.leftSwap_right
#print axioms ShielddSecurity.UserPathSelector964SL03.leftSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.leftSwap_value
#print axioms ShielddSecurity.UserPathSelector964SL03.leftSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.rightSwap_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.rightSwap_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.rightSwap_left
#print axioms ShielddSecurity.UserPathSelector964SL03.rightSwap_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.rightSwap_right
#print axioms ShielddSecurity.UserPathSelector964SL03.rightSwap_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.rightSwap_value
#print axioms ShielddSecurity.UserPathSelector964SL03.rightSwap_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select0_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.select0_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select0_left
#print axioms ShielddSecurity.UserPathSelector964SL03.select0_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select0_right
#print axioms ShielddSecurity.UserPathSelector964SL03.select0_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select0_value
#print axioms ShielddSecurity.UserPathSelector964SL03.select0_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select1_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.select1_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select1_left
#print axioms ShielddSecurity.UserPathSelector964SL03.select1_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select1_right
#print axioms ShielddSecurity.UserPathSelector964SL03.select1_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select1_value
#print axioms ShielddSecurity.UserPathSelector964SL03.select1_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select2_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.select2_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select2_left
#print axioms ShielddSecurity.UserPathSelector964SL03.select2_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select2_right
#print axioms ShielddSecurity.UserPathSelector964SL03.select2_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select2_value
#print axioms ShielddSecurity.UserPathSelector964SL03.select2_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select3_checked
#print axioms ShielddSecurity.UserPathSelector964SL03.select3_checked

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select3_left
#print axioms ShielddSecurity.UserPathSelector964SL03.select3_left

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select3_right
#print axioms ShielddSecurity.UserPathSelector964SL03.select3_right

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.select3_value
#print axioms ShielddSecurity.UserPathSelector964SL03.select3_value

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.child0_shape
#print axioms ShielddSecurity.UserPathSelector964SL03.child0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.child1_shape
#print axioms ShielddSecurity.UserPathSelector964SL03.child1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.child2_shape
#print axioms ShielddSecurity.UserPathSelector964SL03.child2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.child3_shape
#print axioms ShielddSecurity.UserPathSelector964SL03.child3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.inputs_shape
#print axioms ShielddSecurity.UserPathSelector964SL03.inputs_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathSelector964SL03.input_values
#print axioms ShielddSecurity.UserPathSelector964SL03.input_values
