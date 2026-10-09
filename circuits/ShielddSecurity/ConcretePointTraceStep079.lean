import ShielddSecurity.ConcretePointTraceStep078
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep079
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 34230780638816084219016197648746680054417524028721541971713619223918003312354
def inputY : F := 12393090792878025435157954128918680146178636786741959071352274271779375869943
def doubleX : F := 31216228161478164983262073279667801386082596548525135981166972556762718142132
def doubleY : F := 29176811016530637812011142077966937647355777303541981878101397268875118789022
def doubleSlope : F := 3791808004158508190040732425757612110115296956216537104889379800801296700553
def addX : F := 39727463118715422421356341345265883120716365406746825838388955238009483265663
def addY : F := 18278318055383336226248808441008042950102267839158647487505823703875746485647
def addSlope : F := 18329329525359395226923652883753868088397888141277120481828825482420519665646
def outX : F := 39727463118715422421356341345265883120716365406746825838388955238009483265663
def outY : F := 18278318055383336226248808441008042950102267839158647487505823703875746485647

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((547456080901862152745785 : Nat) • base) + ((547456080901862152745785 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep078.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (12393090792878025435157954128918680146178636786741959071352274271779375869943 : Int)) * (12218455463338585389231462838037973379970945937414396150330286258850565905055 : Int) =
        (1 : Int) + (5775604103113063668449013700553443427713669884199995938055874357656597479633 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (3791808004158508190040732425757612110115296956216537104889379800801296700553 : Int) * ((2 : Int) * (12393090792878025435157954128918680146178636786741959071352274271779375869943 : Int)) =
        (3 : Int) * (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) + (-40964 : Int) * (-40964 : Int) + (-65246447709177741611944075279650071618056666478895011013697981717482693231134 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int) =
        (3791808004158508190040732425757612110115296956216537104889379800801296700553 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) - (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) + (-274197920648435674676367787688161207977571012380743959751604159581543220449 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29176811016530637812011142077966937647355777303541981878101397268875118789022 : Int) =
        (3791808004158508190040732425757612110115296956216537104889379800801296700553 : Int) * ((34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) - (31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int)) - (12393090792878025435157954128918680146178636786741959071352274271779375869943 : Int) + (-217992055522095584167038929936504381480948932315620450027488871446158055177 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((547456080901862152745785 : Nat) • base) + ((547456080901862152745785 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (50791792689388125549464070985920773441221532755789720098804705130006840999016 : Int) =
        (1 : Int) + (-8198602253618132280535168219676020710416781122670094006169149727941412973209 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (18329329525359395226923652883753868088397888141277120481828825482420519665646 : Int) * ((31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29176811016530637812011142077966937647355777303541981878101397268875118789022 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2958644977800078272301024605191968170286043973357658424454981647998901297094 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) =
        (18329329525359395226923652883753868088397888141277120481828825482420519665646 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-6407146247242990768987186109722910453099784397680063696190601320666589517062 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (18278318055383336226248808441008042950102267839158647487505823703875746485647 : Int) =
        (18329329525359395226923652883753868088397888141277120481828825482420519665646 : Int) * ((31216228161478164983262073279667801386082596548525135981166972556762718142132 : Int) - (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int)) - (29176811016530637812011142077966937647355777303541981878101397268875118789022 : Int) + (2975162132374658801964485727045138685170002100565374023929086264085158071015 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1094912161803724305491571 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1094912161803724305491571 : Nat) = 547456080901862152745785 + 547456080901862152745785 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep079
