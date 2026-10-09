import ShielddSecurity.ConcretePointTraceStep184
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep185
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 14142225826368604983930400538740523283245533313131970348719988633644542414711
def inputY : F := 25759295944322426411347510914658197928784893813451964358377195658431257035932
def doubleX : F := 37862255749134806676188635197039702004588675458382753068389397604913765690923
def doubleY : F := 7717806057604630173410734524852618806032453212125288469628410750714977513045
def doubleSlope : F := 35568240346740103405460350684541979170460052393233810697037327034993185275618
def outX : F := 37862255749134806676188635197039702004588675458382753068389397604913765690923
def outY : F := 7717806057604630173410734524852618806032453212125288469628410750714977513045

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((44414913891445739055068787299132349446456188403499729424 : Nat) • base) + ((44414913891445739055068787299132349446456188403499729424 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep184.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (25759295944322426411347510914658197928784893813451964358377195658431257035932 : Int)) * (48736852702565146218623983370805331627812232698040967440330892837001081026179 : Int) =
        (1 : Int) + (47884278004985337327411129013055678942329847404775261850884445424986393216935 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (35568240346740103405460350684541979170460052393233810697037327034993185275618 : Int) * ((2 : Int) * (25759295944322426411347510914658197928784893813451964358377195658431257035932 : Int)) =
        (3 : Int) * (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) + (-40964 : Int) * (-40964 : Int) + (23503336227971098512309467364458439273014247340429638248209700308313913503453 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) =
        (35568240346740103405460350684541979170460052393233810697037327034993185275618 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) - (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) + (-24126606395683678093595263255062562530370334387457793676107292875975009186419 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (7717806057604630173410734524852618806032453212125288469628410750714977513045 : Int) =
        (35568240346740103405460350684541979170460052393233810697037327034993185275618 : Int) * ((14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) - (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int)) - (25759295944322426411347510914658197928784893813451964358377195658431257035932 : Int) + (16089742423618945186578291484992070699985042227410304575094693221266148287961 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (88829827782891478110137574598264698892912376806999458848 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (88829827782891478110137574598264698892912376806999458848 : Nat) = 44414913891445739055068787299132349446456188403499729424 + 44414913891445739055068787299132349446456188403499729424 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep185
