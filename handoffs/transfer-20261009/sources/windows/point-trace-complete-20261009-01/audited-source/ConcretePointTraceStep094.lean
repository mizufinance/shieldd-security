import ShielddSecurity.ConcretePointTraceStep093
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep094
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9846380431119359733140617525891122435739757592241736297874683398079559864583
def inputY : F := 25879011625578900460373161622351545339756867977922556523116189900874424182274
def doubleX : F := 24461464705392491042229357040636871938679271236495109094855741519807838645422
def doubleY : F := 20723289146991168259084441554197270236629252679710386347744660745967126570892
def doubleSlope : F := 29148150041117528575619980704220166691786314297172351203128094737332009106688
def outX : F := 24461464705392491042229357040636871938679271236495109094855741519807838645422
def outY : F := 20723289146991168259084441554197270236629252679710386347744660745967126570892

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((17939040858992219021173910532 : Nat) • base) + ((17939040858992219021173910532 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep093.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (25879011625578900460373161622351545339756867977922556523116189900874424182274 : Int)) * (32668880889918169183481255807375894624531503843261831387669802158777025571384 : Int) =
        (1 : Int) + (32246561939558971849628547111834704725861037097441775577488445335949360318687 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (29148150041117528575619980704220166691786314297172351203128094737332009106688 : Int) * ((2 : Int) * (25879011625578900460373161622351545339756867977922556523116189900874424182274 : Int)) =
        (3 : Int) * (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) + (-40964 : Int) * (-40964 : Int) + (23224500415148753904361636076112707509651380031422069826787550469304077760973 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) =
        (29148150041117528575619980704220166691786314297172351203128094737332009106688 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) - (9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) + (-16202926869856618688226220746204194943521622074264885489388648869159206793548 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20723289146991168259084441554197270236629252679710386347744660745967126570892 : Int) =
        (29148150041117528575619980704220166691786314297172351203128094737332009106688 : Int) * ((9846380431119359733140617525891122435739757592241736297874683398079559864583 : Int) - (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int)) - (25879011625578900460373161622351545339756867977922556523116189900874424182274 : Int) + (8124259733766621802523822264442959992376292114716094771005710859312659093646 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (35878081717984438042347821064 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (35878081717984438042347821064 : Nat) = 17939040858992219021173910532 + 17939040858992219021173910532 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep094
