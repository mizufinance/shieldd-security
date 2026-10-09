import ShielddSecurity.ConcretePointTraceStep171
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep172
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 1768503296666626415548150318257779985916935307768164737224397343752491127180
def inputY : F := 33148334770121454971270983107082426799765682846177826899308707417511807605290
def doubleX : F := 4384458270312404527472311720528415181244761365469771907195408673353958364732
def doubleY : F := 40818718863369315974009069930431336203247929834174035758463127960833108865186
def doubleSlope : F := 38370790240502643450426848167215445331245070943700727480368049832516431636245
def outX : F := 4384458270312404527472311720528415181244761365469771907195408673353958364732
def outY : F := 40818718863369315974009069930431336203247929834174035758463127960833108865186

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5421742418389372443245701574601116875788108935974088 : Nat) • base) + ((5421742418389372443245701574601116875788108935974088 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep171.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33148334770121454971270983107082426799765682846177826899308707417511807605290 : Int)) * (8926608941878350482801206472703015224414444811670975153486963242024586154116 : Int) =
        (1 : Int) + (11286250895177553665997477364999699288791639411774586552630273547657039067983 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (38370790240502643450426848167215445331245070943700727480368049832516431636245 : Int) * ((2 : Int) * (33148334770121454971270983107082426799765682846177826899308707417511807605290 : Int)) =
        (3 : Int) * (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) + (-40964 : Int) * (-40964 : Int) + (48334709402235508043099054862979450290433951540064644864080694212621824426468 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) =
        (38370790240502643450426848167215445331245070943700727480368049832516431636245 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) - (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) + (-28078439403621714771416364677199435378249683095280217159083850159125773741677 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (40818718863369315974009069930431336203247929834174035758463127960833108865186 : Int) =
        (38370790240502643450426848167215445331245070943700727480368049832516431636245 : Int) * ((1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) - (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int)) - (33148334770121454971270983107082426799765682846177826899308707417511807605290 : Int) + (1914266887643688696609937672152764490230812806143201156385541599624923299132 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (10843484836778744886491403149202233751576217871948176 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (10843484836778744886491403149202233751576217871948176 : Nat) = 5421742418389372443245701574601116875788108935974088 + 5421742418389372443245701574601116875788108935974088 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep172
