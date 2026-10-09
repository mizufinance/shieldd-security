import ShielddSecurity.ConcretePointTraceStep062
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep063
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9867187175390698469449111545990037690958776529031944726895092268896072123358
def inputY : F := 11657355169897232660018591063280301913857762733400665118460616232932926488131
def doubleX : F := 37176356966639490230540366278156516828193009809942079545520782342339950640546
def doubleY : F := 2202401624001785122677968684357280230372150033801081057322749784389811960889
def doubleSlope : F := 1986255933250848950212566824199100858532350222071561949645091326519322836881
def outX : F := 37176356966639490230540366278156516828193009809942079545520782342339950640546
def outY : F := 2202401624001785122677968684357280230372150033801081057322749784389811960889

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((8353516859464449352 : Nat) • base) + ((8353516859464449352 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep062.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (11657355169897232660018591063280301913857762733400665118460616232932926488131 : Int)) * (25706112120498482451989689591992571300796550281426519329431363193706298395545 : Int) =
        (1 : Int) + (11429780776044031532345374580076927441634191622077462218423048607302801567253 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (1986255933250848950212566824199100858532350222071561949645091326519322836881 : Int) * ((2 : Int) * (11657355169897232660018591063280301913857762733400665118460616232932926488131 : Int)) =
        (3 : Int) * (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) + (-40964 : Int) * (-40964 : Int) + (-4687156754746601090249430509960363230834526127802158643431820722949994126806 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) =
        (1986255933250848950212566824199100858532350222071561949645091326519322836881 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) - (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) + (-75238805859498205645644677290936616460041372350139881939866232057124154059 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2202401624001785122677968684357280230372150033801081057322749784389811960889 : Int) =
        (1986255933250848950212566824199100858532350222071561949645091326519322836881 : Int) * ((9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) - (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int)) - (11657355169897232660018591063280301913857762733400665118460616232932926488131 : Int) + (1034463529956563202132996621162710071525736970211741328282833716717007072896 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (16707033718928898704 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (16707033718928898704 : Nat) = 8353516859464449352 + 8353516859464449352 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep063
