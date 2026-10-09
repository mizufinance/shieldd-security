import ShielddSecurity.ConcretePointTraceStep197
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep198
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22427083887566916763150712603740354714112708205669018249526835344052679667908
def inputY : F := 20238679198938448964410743809584059456647769868887049665308287247699376974501
def doubleX : F := 36547485582606558598401671945885162598989470817915298856933435255016242542972
def doubleY : F := 23838545710886353957359568032953173671398394694985585110808103288504335462039
def doubleSlope : F := 36987809421981326929959540025266329711857415503683362387147451417439642135497
def outX : F := 36547485582606558598401671945885162598989470817915298856933435255016242542972
def outY : F := 23838545710886353957359568032953173671398394694985585110808103288504335462039

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((363846974598723494339123505554492206665369095401469783444290 : Nat) • base) + ((363846974598723494339123505554492206665369095401469783444290 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep197.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (20238679198938448964410743809584059456647769868887049665308287247699376974501 : Int)) * (11875632525101230487998216602558601020361433012420339235607709193831954709919 : Int) =
        (1 : Int) + (9167277790531308692961004125890631373985359642857322365700719988592159496949 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36987809421981326929959540025266329711857415503683362387147451417439642135497 : Int) * ((2 : Int) * (20238679198938448964410743809584059456647769868887049665308287247699376974501 : Int)) =
        (3 : Int) * (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) + (-40964 : Int) * (-40964 : Int) + (-224149148550116216970850715853332802747248804660140677193621587396935340262 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) =
        (36987809421981326929959540025266329711857415503683362387147451417439642135497 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) - (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) + (-26090878454257022929734757677637338177293683109728717600267083155125711472853 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (23838545710886353957359568032953173671398394694985585110808103288504335462039 : Int) =
        (36987809421981326929959540025266329711857415503683362387147451417439642135497 : Int) * ((22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) - (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int)) - (20238679198938448964410743809584059456647769868887049665308287247699376974501 : Int) + (9960408310410000799369017182489355634674146741599900539849681675070876047796 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (727693949197446988678247011108984413330738190802939566888580 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (727693949197446988678247011108984413330738190802939566888580 : Nat) = 363846974598723494339123505554492206665369095401469783444290 + 363846974598723494339123505554492206665369095401469783444290 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep198
