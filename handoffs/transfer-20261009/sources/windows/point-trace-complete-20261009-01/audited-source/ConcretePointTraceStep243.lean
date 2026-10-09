import ShielddSecurity.ConcretePointTraceStep242
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep243
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 50913547063236267894845220072698185523678018183223156874149214014707768159028
def inputY : F := 21401289352551848955399592228220798903483060655581350929226333492081455390711
def doubleX : F := 37358642005473444203882245883233558319416201610318860048502099871968502082644
def doubleY : F := 12885287475909511778264964871177193019118005193927893854938256900211065153502
def doubleSlope : F := 2095439996571531898285641670824193258202384382664520709451543172511235538833
def outX : F := 37358642005473444203882245883233558319416201610318860048502099871968502082644
def outY : F := 12885287475909511778264964871177193019118005193927893854938256900211065153502

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((12801727337677292597521421022506339315831877472406869690166717114047232918 : Nat) • base) + ((12801727337677292597521421022506339315831877472406869690166717114047232918 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep242.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21401289352551848955399592228220798903483060655581350929226333492081455390711 : Int)) * (41490403938696596256999967992585630884012096849620092121616940503824517517046 : Int) =
        (1 : Int) + (33867962995972474681292978488872788700660571293499866988901386958205996692147 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (2095439996571531898285641670824193258202384382664520709451543172511235538833 : Int) * ((2 : Int) * (21401289352551848955399592228220798903483060655581350929226333492081455390711 : Int)) =
        (3 : Int) * (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) + (-40964 : Int) * (-40964 : Int) + (-146595771742786573785823404691979455932546026156454843144734042595962209766578 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) =
        (2095439996571531898285641670824193258202384382664520709451543172511235538833 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) - (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) + (-83737875349024050898822344560360870715380382218601268143631906338146561389 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (12885287475909511778264964871177193019118005193927893854938256900211065153502 : Int) =
        (2095439996571531898285641670824193258202384382664520709451543172511235538833 : Int) * ((50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) - (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int)) - (21401289352551848955399592228220798903483060655581350929226333492081455390711 : Int) + (-541680483312303497617522667359343366671531394563844270939295515238671103243 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) = 12801727337677292597521421022506339315831877472406869690166717114047232918 + 12801727337677292597521421022506339315831877472406869690166717114047232918 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep243
