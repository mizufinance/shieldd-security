import ShielddSecurity.ConcretePointTraceStep033
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep034
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 24851920105061636754870529796747350313026361476967296100868617233016623517151
def inputY : F := 39527505731992063567627203920232128899227990453209890860340527769887280618093
def doubleX : F := 45466447067294891010862106179202775952771623178765382482196860805216651862813
def doubleY : F := 18625121304602990171159681503757143764427980449603755414902894215780626446621
def doubleSlope : F := 41488284694487033914486113904649645440492682617586969799564763980817104822854
def outX : F := 45466447067294891010862106179202775952771623178765382482196860805216651862813
def outY : F := 18625121304602990171159681503757143764427980449603755414902894215780626446621

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((15559637657 : Nat) • base) + ((15559637657 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep033.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (39527505731992063567627203920232128899227990453209890860340527769887280618093 : Int)) * (12196939113525585219374012691961103271037556328942842728874362489446021908765 : Int) =
        (1 : Int) + (18388730200934632420380332233116039913028594680975215684510370962866120664753 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41488284694487033914486113904649645440492682617586969799564763980817104822854 : Int) * ((2 : Int) * (39527505731992063567627203920232128899227990453209890860340527769887280618093 : Int)) =
        (3 : Int) * (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) + (-40964 : Int) * (-40964 : Int) + (27214250141771856164769709724199330496596389225100038479906271800275960958137 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) =
        (41488284694487033914486113904649645440492682617586969799564763980817104822854 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) - (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) + (-32826338096619071175691071139484084812700566847597528027244461908287122271313 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (18625121304602990171159681503757143764427980449603755414902894215780626446621 : Int) =
        (41488284694487033914486113904649645440492682617586969799564763980817104822854 : Int) * ((24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) - (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int)) - (39527505731992063567627203920232128899227990453209890860340527769887280618093 : Int) + (16310614833735422020872281077131147370922842519704957769382322748047987547774 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (31119275314 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (31119275314 : Nat) = 15559637657 + 15559637657 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep034
