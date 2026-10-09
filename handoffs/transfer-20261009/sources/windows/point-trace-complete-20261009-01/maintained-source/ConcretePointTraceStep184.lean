import ShielddSecurity.ConcretePointTraceStep183
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep184
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 43757500933763341425818136817149715342039627569793424573198778816067373963464
def inputY : F := 48008767005075130188619138434974610680629315432845505254802505996585524882135
def doubleX : F := 14142225826368604983930400538740523283245533313131970348719988633644542414711
def doubleY : F := 25759295944322426411347510914658197928784893813451964358377195658431257035932
def doubleSlope : F := 18495062528438238947222696723889601330179517930082886879536215904410172436225
def outX : F := 14142225826368604983930400538740523283245533313131970348719988633644542414711
def outY : F := 25759295944322426411347510914658197928784893813451964358377195658431257035932

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((22207456945722869527534393649566174723228094201749864712 : Nat) • base) + ((22207456945722869527534393649566174723228094201749864712 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep183.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (48008767005075130188619138434974610680629315432845505254802505996585524882135 : Int)) * (8666017564877810733748399432750953453957736425477984260784343927350000574133 : Int) =
        (1 : Int) + (15868708846551873208301401989817900129293354913563325639634264578233663551493 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (18495062528438238947222696723889601330179517930082886879536215904410172436225 : Int) * ((2 : Int) * (48008767005075130188619138434974610680629315432845505254802505996585524882135 : Int)) =
        (3 : Int) * (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) + (-40964 : Int) * (-40964 : Int) + (-75679224487191460658004621589216212143961106413404707853226007885081522536610 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int) =
        (18495062528438238947222696723889601330179517930082886879536215904410172436225 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) - (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) + (-6523536353467891862381421785925121892336820085941543590503098734475458944258 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25759295944322426411347510914658197928784893813451964358377195658431257035932 : Int) =
        (18495062528438238947222696723889601330179517930082886879536215904410172436225 : Int) * ((43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) - (14142225826368604983930400538740523283245533313131970348719988633644542414711 : Int)) - (48008767005075130188619138434974610680629315432845505254802505996585524882135 : Int) + (-10445832420624759183380593525559423209751616798814301215342114711914471225566 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (44414913891445739055068787299132349446456188403499729424 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (44414913891445739055068787299132349446456188403499729424 : Nat) = 22207456945722869527534393649566174723228094201749864712 + 22207456945722869527534393649566174723228094201749864712 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep184
