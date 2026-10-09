import ShielddSecurity.ConcretePointTraceStep094
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep095
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 24461464705392491042229357040636871938679271236495109094855741519807838645422
def inputY : F := 20723289146991168259084441554197270236629252679710386347744660745967126570892
def doubleX : F := 49393179351466391995761064388693349660702318992644268865906573818445418094611
def doubleY : F := 44746577926508209360648586694486424036840657692962498918737905330322941858290
def doubleSlope : F := 25646189485187271048224704023163162147372093571647812586393280930176812141227
def outX : F := 49393179351466391995761064388693349660702318992644268865906573818445418094611
def outY : F := 44746577926508209360648586694486424036840657692962498918737905330322941858290

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((35878081717984438042347821064 : Nat) • base) + ((35878081717984438042347821064 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep094.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (20723289146991168259084441554197270236629252679710386347744660745967126570892 : Int)) * (29733134221331240816394476946239350289127572788851743533459965001933061203418 : Int) =
        (1 : Int) + (23501785205531760349526723728292907767124239026632084076761151125132464411247 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25646189485187271048224704023163162147372093571647812586393280930176812141227 : Int) * ((2 : Int) * (20723289146991168259084441554197270236629252679710386347744660745967126570892 : Int)) =
        (3 : Int) * (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) + (-40964 : Int) * (-40964 : Int) + (-13962634622081615946383312738431018912352206566792671243643876297155237561076 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) =
        (25646189485187271048224704023163162147372093571647812586393280930176812141227 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) - (24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) + (-12543454894448555911103359673018811193138494870576119456832184246468398798034 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44746577926508209360648586694486424036840657692962498918737905330322941858290 : Int) =
        (25646189485187271048224704023163162147372093571647812586393280930176812141227 : Int) * ((24461464705392491042229357040636871938679271236495109094855741519807838645422 : Int) - (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int)) - (20723289146991168259084441554197270236629252679710386347744660745967126570892 : Int) + (12194007935756575188990409311799772598310004843998296297948705786280960557045 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (71756163435968876084695642128 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (71756163435968876084695642128 : Nat) = 35878081717984438042347821064 + 35878081717984438042347821064 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep095
