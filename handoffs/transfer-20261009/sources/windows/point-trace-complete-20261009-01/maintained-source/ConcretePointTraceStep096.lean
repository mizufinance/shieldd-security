import ShielddSecurity.ConcretePointTraceStep095
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep096
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 49393179351466391995761064388693349660702318992644268865906573818445418094611
def inputY : F := 44746577926508209360648586694486424036840657692962498918737905330322941858290
def doubleX : F := 15611642098156039252064818416207076062796636688516952229883971198268621294812
def doubleY : F := 24588131983877049843316893137041728949182892660697546954365693295357765833005
def doubleSlope : F := 33103802680414287720935155770675619008465138244674146287404413573946914111383
def outX : F := 15611642098156039252064818416207076062796636688516952229883971198268621294812
def outY : F := 24588131983877049843316893137041728949182892660697546954365693295357765833005

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((71756163435968876084695642128 : Nat) • base) + ((71756163435968876084695642128 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep095.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (44746577926508209360648586694486424036840657692962498918737905330322941858290 : Int)) * (29238833020223803291183780141279215034427917923072051495403579379118109208360 : Int) =
        (1 : Int) + (49902388997990332231266968093661239082168523458423239166731845194381993605023 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (33103802680414287720935155770675619008465138244674146287404413573946914111383 : Int) * ((2 : Int) * (44746577926508209360648586694486424036840657692962498918737905330322941858290 : Int)) =
        (3 : Int) * (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) + (-40964 : Int) * (-40964 : Int) + (-83082330793233968783214472126414171980214371944401966632444504843352562695071 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) =
        (33103802680414287720935155770675619008465138244674146287404413573946914111383 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) - (49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) + (-20899083847534292916902790226312062400003672185022149851972348975049665781271 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24588131983877049843316893137041728949182892660697546954365693295357765833005 : Int) =
        (33103802680414287720935155770675619008465138244674146287404413573946914111383 : Int) * ((49393179351466391995761064388693349660702318992644268865906573818445418094611 : Int) - (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int)) - (44746577926508209360648586694486424036840657692962498918737905330322941858290 : Int) + (-21326951056690532522000094073329108670199367214758662355604066839874817440594 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (143512326871937752169391284256 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (143512326871937752169391284256 : Nat) = 71756163435968876084695642128 + 71756163435968876084695642128 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep096
