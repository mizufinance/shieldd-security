import ShielddSecurity.ConcretePointTraceStep098
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep099
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25648222042139526187058982145541136937958275570726066717454523071661825287298
def inputY : F := 15516335090179794014609132870884930266416327652082493352988931366130994621079
def doubleX : F := 17914789876360216820314058796427786218320602461974434137234118359723419076246
def doubleY : F := 36301073299666131014736251954932608014472669558439586020884423532763121669055
def doubleSlope : F := 10993006610810471744868769972051341871980053237503029356978881648092384984246
def addX : F := 13239922607602991637023780189025675452565898633239401588429543605532877284469
def addY : F := 36047738064920237178441897142007024680571271339858281647969177837624305380552
def addSlope : F := 31432009058135977458377978754980934246593409586579357564583392261385281330469
def outX : F := 13239922607602991637023780189025675452565898633239401588429543605532877284469
def outY : F := 36047738064920237178441897142007024680571271339858281647969177837624305380552

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((574049307487751008677565137024 : Nat) • base) + ((574049307487751008677565137024 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep098.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15516335090179794014609132870884930266416327652082493352988931366130994621079 : Int)) * (7007699635426391986787832042184818539547728151960222628018835213251963592305 : Int) =
        (1 : Int) + (4147306224658431106918813794759791627831531983611216157039358929026013855053 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10993006610810471744868769972051341871980053237503029356978881648092384984246 : Int) * ((2 : Int) * (15516335090179794014609132870884930266416327652082493352988931366130994621079 : Int)) =
        (3 : Int) * (25648222042139526187058982145541136937958275570726066717454523071661825287298 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25648222042139526187058982145541136937958275570726066717454523071661825287298 : Int) + (-40964 : Int) * (-40964 : Int) + (-31130433655834432842012741977318538841913565879835935983836110255183734724424 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int) =
        (10993006610810471744868769972051341871980053237503029356978881648092384984246 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25648222042139526187058982145541136937958275570726066717454523071661825287298 : Int) - (25648222042139526187058982145541136937958275570726066717454523071661825287298 : Int) + (-2304647227527311125100879579675853041483228457159057073073560197235660833234 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36301073299666131014736251954932608014472669558439586020884423532763121669055 : Int) =
        (10993006610810471744868769972051341871980053237503029356978881648092384984246 : Int) * ((25648222042139526187058982145541136937958275570726066717454523071661825287298 : Int) - (17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int)) - (15516335090179794014609132870884930266416327652082493352988931366130994621079 : Int) + (-1621288300018570268541015700714946823052329680911883891821779640279462647666 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((574049307487751008677565137024 : Nat) • base) + ((574049307487751008677565137024 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (33861347182895462146624742542319012587212856592264650393767275574088881989036 : Int) =
        (1 : Int) + (-14055386582851675087633505027168322249124643375724510419887314856472134591741 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (31432009058135977458377978754980934246593409586579357564583392261385281330469 : Int) * ((17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (36301073299666131014736251954932608014472669558439586020884423532763121669055 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-13047001231272914652443791399056766755506118175133147309056169992526236017574 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) =
        (31432009058135977458377978754980934246593409586579357564583392261385281330469 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-18841512421240226153713711140302098778322192733722461711910272306424800728387 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (36047738064920237178441897142007024680571271339858281647969177837624305380552 : Int) =
        (31432009058135977458377978754980934246593409586579357564583392261385281330469 : Int) * ((17914789876360216820314058796427786218320602461974434137234118359723419076246 : Int) - (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int)) - (36301073299666131014736251954932608014472669558439586020884423532763121669055 : Int) + (-2802288888025732789826649735227335912014595107382065843216796747761711328062 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1148098614975502017355130274049 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1148098614975502017355130274049 : Nat) = 574049307487751008677565137024 + 574049307487751008677565137024 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep099
