import ShielddSecurity.ConcretePointTraceStep168
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep169
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32813600355130895053914219587385840934503052564880347515933484622823044827327
def inputY : F := 32471264338507219449362255029578969297361792534565272293444715920611648997732
def doubleX : F := 3147633108254557659267076243015408644111025977049840848883617385222848040768
def doubleY : F := 4699053524926918604632582460225994935048322750747739167969929053209420964540
def doubleSlope : F := 1388019192937727107560318254721529857719101120368861625430461437379098441426
def outX : F := 3147633108254557659267076243015408644111025977049840848883617385222848040768
def outY : F := 4699053524926918604632582460225994935048322750747739167969929053209420964540

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((677717802298671555405712696825139609473513616996761 : Nat) • base) + ((677717802298671555405712696825139609473513616996761 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep168.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (32471264338507219449362255029578969297361792534565272293444715920611648997732 : Int)) * (27529663142606234350894821060561146311912287026281136764666295741899200044247 : Int) =
        (1 : Int) + (34095853881263082031157281503119701307443151777641218987580820866530951669239 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (1388019192937727107560318254721529857719101120368861625430461437379098441426 : Int) * ((2 : Int) * (32471264338507219449362255029578969297361792534565272293444715920611648997732 : Int)) =
        (3 : Int) * (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) + (-40964 : Int) * (-40964 : Int) + (-59883726896326712635361671984982595600570963046489882364642041744644250032019 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) =
        (1388019192937727107560318254721529857719101120368861625430461437379098441426 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) - (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) + (-36741968614598656263368873199901020241468311746828231052657885198888772494 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (4699053524926918604632582460225994935048322750747739167969929053209420964540 : Int) =
        (1388019192937727107560318254721529857719101120368861625430461437379098441426 : Int) * ((32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) - (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int)) - (32471264338507219449362255029578969297361792534565272293444715920611648997732 : Int) + (-785281675536127731707923566996178141115133737505328859967582844362819471374 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1355435604597343110811425393650279218947027233993522 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1355435604597343110811425393650279218947027233993522 : Nat) = 677717802298671555405712696825139609473513616996761 + 677717802298671555405712696825139609473513616996761 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep169
