import ShielddSecurity.ConcretePointTraceStep092
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep093
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 51173066641752700007264529121140433676795022166350596130073961272919411352843
def inputY : F := 11732452124096413568853259860659433381095630581913234171290409685136186289477
def doubleX : F := 9846380431119359733140617525891122435739757592241736297874683398079559864583
def doubleY : F := 25879011625578900460373161622351545339756867977922556523116189900874424182274
def doubleSlope : F := 6942286378613538993613355060403268295562220224392745793408005861478032996958
def outX : F := 9846380431119359733140617525891122435739757592241736297874683398079559864583
def outY : F := 25879011625578900460373161622351545339756867977922556523116189900874424182274

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((8969520429496109510586955266 : Nat) • base) + ((8969520429496109510586955266 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep092.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (11732452124096413568853259860659433381095630581913234171290409685136186289477 : Int)) * (5614789667426213831259606676641294774834592313163783558524212650379473476756 : Int) =
        (1 : Int) + (2512602325790807962497610559765996864782450064346278566311367500336374345671 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (6942286378613538993613355060403268295562220224392745793408005861478032996958 : Int) * ((2 : Int) * (11732452124096413568853259860659433381095630581913234171290409685136186289477 : Int)) =
        (3 : Int) * (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) + (-40964 : Int) * (-40964 : Int) + (-146715357333741207351974043320730322024199297327249554140036730821466958673951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) =
        (6942286378613538993613355060403268295562220224392745793408005861478032996958 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) - (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) + (-919129126799533776154978832573716455554388025531036383794731678127393283951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25879011625578900460373161622351545339756867977922556523116189900874424182274 : Int) =
        (6942286378613538993613355060403268295562220224392745793408005861478032996958 : Int) * ((51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) - (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int)) - (11732452124096413568853259860659433381095630581913234171290409685136186289477 : Int) + (-5471477109805393118147044159766775048897987658340038934956839960583591734833 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (17939040858992219021173910532 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (17939040858992219021173910532 : Nat) = 8969520429496109510586955266 + 8969520429496109510586955266 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep093
