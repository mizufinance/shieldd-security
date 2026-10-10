import ShielddSecurity.ConcretePointCoordinateRows01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteEightTorsionData01
open TorsionCertifiedField01 ConcretePointTorsion01 ConcretePointCoordinateRows01

def X1 : F := 40969977092314373855427314892644412412056592297350547336836035604665542479344
def Y1 : F := 8517375676716710632729603094128566137031651800514311879456805911809224835820
def X2 : F := 52435875175126190479447740508185965837690552500527637822603658699938581143549
def Y2 : F := 5814683835930934717671286667476817164905481252953977631210752442368
def X3 : F := 37748634194707046026986136096002964518686894419990801728560193225894679879758
def Y3 : F := 379913441938374906258112301994250146405240686971784585378617583905548416886
def S1 : F := 21436686025926085348661322428316123424296062828065622467326714665490799416805
def S2 : F := 52435875175126048533255085227092379486585497407832468759981528195651128524801
def S3 : F := 17814886934372270897273405986931121923522424736541908542013591526491023390937

theorem equation1 : curve.Equation X1 Y1 := by
  apply (equation_iff X1 Y1).mpr
  unfold right
  have integer : (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int) * (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int) = (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) + ((40962 : Int) * (-40964 : Int)) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) + ((-40964 : Int) * (-40964 : Int)) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) + (-1311501049404145013763871464062574922832754590371408676081465599710232437038341325220312694141980863709188312445453398644972712943508409269160297625828720 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem equation2 : curve.Equation X2 Y2 := by
  apply (equation_iff X2 Y2).mpr
  unfold right
  have integer : (5814683835930934717671286667476817164905481252953977631210752442368 : Int) * (5814683835930934717671286667476817164905481252953977631210752442368 : Int) = (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + ((40962 : Int) * (-40964 : Int)) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + ((-40964 : Int) * (-40964 : Int)) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + (-2749521005381415097082206172483163991323504094851844918096251953255183978191492345968093606590691993505415715679557231025287894691868077863879009346412397 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem equation3 : curve.Equation X3 Y3 := by
  apply (equation_iff X3 Y3).mpr
  unfold right
  have integer : (379913441938374906258112301994250146405240686971784585378617583905548416886 : Int) * (379913441938374906258112301994250146405240686971784585378617583905548416886 : Int) = (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) * (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) * (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) + ((40962 : Int) * (-40964 : Int)) * (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) * (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) + ((-40964 : Int) * (-40964 : Int)) * (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) + (-1025829555297613295438666926516897081199091971678711334218721275755170403824460281072973223652709835337470507178392896243048868646228412253897456925612564 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double1_nonzero : (2 : F) * Y1 ≠ 0 := by
  have integer : ((2 : Int) * (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int)) * (6805949766023750207469435045338135131244259221193363223242354623351803662825 : Int) = 1 + (2211037035254250313244826028587652392639289540952915182934846457762162518423 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_nonzero _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double1_slope : S1 * (2 * Y1) = 3 * X1 ^ 2 + 2 * (A * B) * X1 + B * B := by
  have integer : (21436686025926085348661322428316123424296062828065622467326714665490799416805 : Int) * ((2 : Int) * (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int)) = (3 : Int) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) + (-40964 : Int) * (-40964 : Int) + (-89069714903061732415144722266816162993195611449059067222380763024766001082840 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double1_x : (X2 : F) = S1 ^ 2 - A * B - X1 - X1 := by
  have integer : (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) = (21436686025926085348661322428316123424296062828065622467326714665490799416805 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) + (-8763685286826698009451021042703615927348427407900410196178374987628940043012 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double1_y : (Y2 : F) = S1 * (X1 - X2) - Y1 := by
  have integer : (5814683835930934717671286667476817164905481252953977631210752442368 : Int) = (21436686025926085348661322428316123424296062828065622467326714665490799416805 : Int) * ((40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int)) - (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int) + (4687455990495218239368435061555754006711637646086812563084891162406725269901 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double2_nonzero : (2 : F) * Y2 ≠ 0 := by
  have integer : ((2 : Int) * (5814683835930934717671286667476817164905481252953977631210752442368 : Int)) * (24463304757087164571729133986487142679091601877399112263012102410304375368475 : Int) = 1 + (5425536706287834040693106012787534184956769596218676355417321242623 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_nonzero _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double2_slope : S2 * (2 * Y2) = 3 * X2 ^ 2 + 2 * (A * B) * X2 + B * B := by
  have integer : (52435875175126048533255085227092379486585497407832468759981528195651128524801 : Int) * ((2 : Int) * (5814683835930934717671286667476817164905481252953977631210752442368 : Int)) = (3 : Int) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + (-40964 : Int) * (-40964 : Int) + (-157307625513749203766481383570418956157548485754125527926915134822239546949723 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double2_x : (0 : F) = S2 ^ 2 - A * B - X2 - X2 := by
  have integer : (0 : Int) = (52435875175126048533255085227092379486585497407832468759981528195651128524801 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + (-52435875175125906587062429946383047647148973592143724284520868886974271127567 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem double2_y : (0 : F) = S2 * (X2 - 0) - Y2 := by
  have integer : (0 : Int) = (52435875175126048533255085227092379486585497407832468759981528195651128524801 : Int) * ((52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) - (0 : Int)) - (5814683835930934717671286667476817164905481252953977631210752442368 : Int) + (-52435875175126048533255085227092379486585497407832468759981528195651128483837 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem add13_different : X1 ≠ X2 := by
  have integer : ((40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int)) * (24599977795153295913414172226449159153043835605193945765684459879618897970362 : Int) = 1 + (-5379157633902934794553766930403672841998236086095086331158510120169312997747 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_nonzero _ _ _ integer
  apply sub_ne_zero.mp
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem add13_slope : S3 * (X1 - X2) = Y1 - Y2 := by
  have integer : (17814886934372270897273405986931121923522424736541908542013591526491023390937 : Int) * ((40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int)) = (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int) - (5814683835930934717671286667476817164905481252953977631210752442368 : Int) + (-3895494778415066813455257340079406532619577099354673351623715187074484004849 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem add13_x : X3 = S3 ^ 2 - A * B - X1 - X2 := by
  have integer : (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int) = (17814886934372270897273405986931121923522424736541908542013591526491023390937 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (52435875175126190479447740508185965837690552500527637822603658699938581143549 : Int) + (-6052539323974467741959622158716266354173538713192035641400350463487981541822 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

theorem add13_y : Y3 = S3 * (X1 - X3) - Y1 := by
  have integer : (379913441938374906258112301994250146405240686971784585378617583905548416886 : Int) = (17814886934372270897273405986931121923522424736541908542013591526491023390937 : Int) * ((40969977092314373855427314892644412412056592297350547336836035604665542479344 : Int) - (37748634194707046026986136096002964518686894419990801728560193225894679879758 : Int)) - (8517375676716710632729603094128566137031651800514311879456805911809224835820 : Int) + (-1094438860914455764871934534040482248915126159085030021412888902734598611952 : Int) * (TorsionEulerInteger49.modulus : Int) := by decide +kernel
  have equal := field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero, Int.cast_one, A, B, X1, Y1, X2, Y2, X3, Y3, S1, S2, S3] using equal

end ShielddSecurity.ConcreteEightTorsionData01

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.equation1
#print axioms ShielddSecurity.ConcreteEightTorsionData01.equation1

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.equation2
#print axioms ShielddSecurity.ConcreteEightTorsionData01.equation2

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.equation3
#print axioms ShielddSecurity.ConcreteEightTorsionData01.equation3

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double1_nonzero
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double1_nonzero

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double1_slope
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double1_slope

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double1_x
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double1_x

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double1_y
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double1_y

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double2_nonzero
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double2_nonzero

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double2_slope
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double2_slope

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double2_x
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double2_x

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.double2_y
#print axioms ShielddSecurity.ConcreteEightTorsionData01.double2_y

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.add13_different
#print axioms ShielddSecurity.ConcreteEightTorsionData01.add13_different

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.add13_slope
#print axioms ShielddSecurity.ConcreteEightTorsionData01.add13_slope

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.add13_x
#print axioms ShielddSecurity.ConcreteEightTorsionData01.add13_x

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionData01.add13_y
#print axioms ShielddSecurity.ConcreteEightTorsionData01.add13_y
