import ShielddSecurity.ConcretePointTraceStep119
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep120
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10767247375270118000210438247922729357708414268174687085759883470528384585428
def inputY : F := 10327454339289633618115030706699013079743701626655483760299762745623047179222
def doubleX : F := 48705534063244610064759631108664746030543742969253284874080975800752547122750
def doubleY : F := 9891881026777460469533128640819386919201948907094010748863505415786872805842
def doubleSlope : F := 15176071493103941268063333065403263345950868628496118368882284402974328153479
def outX : F := 48705534063244610064759631108664746030543742969253284874080975800752547122750
def outY : F := 9891881026777460469533128640819386919201948907094010748863505415786872805842

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1203868653296552003350173082241418160 : Nat) • base) + ((1203868653296552003350173082241418160 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep119.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (10327454339289633618115030706699013079743701626655483760299762745623047179222 : Int)) * (47282020318278192245364574686709075282289045758235189233118175468585376572841 : Int) =
        (1 : Int) + (18624764220127564836311262270249907553529476100678152395636331237017191611531 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15176071493103941268063333065403263345950868628496118368882284402974328153479 : Int) * ((2 : Int) * (10327454339289633618115030706699013079743701626655483760299762745623047179222 : Int)) =
        (3 : Int) * (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) + (-40964 : Int) * (-40964 : Int) + (-654904246690664270432087339052478984914688184359759683244078807583784327628 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) =
        (15176071493103941268063333065403263345950868628496118368882284402974328153479 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) - (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) + (-4392281909944260315653818791917982670494523448724033113802737668068870562131 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (9891881026777460469533128640819386919201948907094010748863505415786872805842 : Int) =
        (15176071493103941268063333065403263345950868628496118368882284402974328153479 : Int) * ((10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) - (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int)) - (10327454339289633618115030706699013079743701626655483760299762745623047179222 : Int) + (10980157176354191312683900001093109193322432742765421775205369299256163674254 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2407737306593104006700346164482836320 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2407737306593104006700346164482836320 : Nat) = 1203868653296552003350173082241418160 + 1203868653296552003350173082241418160 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


set_option pp.all true in
#check @baseX
#print axioms baseX

set_option pp.all true in
#check @baseY
#print axioms baseY

set_option pp.all true in
#check @inputX
#print axioms inputX

set_option pp.all true in
#check @inputY
#print axioms inputY

set_option pp.all true in
#check @doubleX
#print axioms doubleX

set_option pp.all true in
#check @doubleY
#print axioms doubleY

set_option pp.all true in
#check @doubleSlope
#print axioms doubleSlope

set_option pp.all true in
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep120
