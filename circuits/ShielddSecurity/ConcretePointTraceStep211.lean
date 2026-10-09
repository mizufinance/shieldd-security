import ShielddSecurity.ConcretePointTraceStep210
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep211
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 51416991987979403886768393919473314696421406857084890008516249377944912691716
def inputY : F := 7219116586605449134138994123065718562687353888322121594704762768593102939856
def doubleX : F := 39616757784064212658529686082734329854694375587113872326623701052229305486427
def doubleY : F := 10338479386250041285497246485137909591009928583279502863946188197271445088555
def doubleSlope : F := 36588670326114017083232114363273344736854176428073098683085659912854566791150
def outX : F := 39616757784064212658529686082734329854694375587113872326623701052229305486427
def outY : F := 10338479386250041285497246485137909591009928583279502863946188197271445088555

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2980634415912742865626099757502400157002703629528840465975626631 : Nat) • base) + ((2980634415912742865626099757502400157002703629528840465975626631 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep210.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7219116586605449134138994123065718562687353888322121594704762768593102939856 : Int)) * (51509914270853816339577643224853077389702919443335568830089642322242294206827 : Int) =
        (1 : Int) + (14183269574329198487319591356553059073769875900595545060356125135010277691871 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36588670326114017083232114363273344736854176428073098683085659912854566791150 : Int) * ((2 : Int) * (7219116586605449134138994123065718562687353888322121594704762768593102939856 : Int)) =
        (3 : Int) * (51416991987979403886768393919473314696421406857084890008516249377944912691716 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (51416991987979403886768393919473314696421406857084890008516249377944912691716 : Int) + (-40964 : Int) * (-40964 : Int) + (-141179019457298923023131557266526112980025406292667251815663430553112035296576 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) =
        (36588670326114017083232114363273344736854176428073098683085659912854566791150 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51416991987979403886768393919473314696421406857084890008516249377944912691716 : Int) - (51416991987979403886768393919473314696421406857084890008516249377944912691716 : Int) + (-25530818199599825159713018345410530589085965178166826045468795351392906793193 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (10338479386250041285497246485137909591009928583279502863946188197271445088555 : Int) =
        (36588670326114017083232114363273344736854176428073098683085659912854566791150 : Int) * ((51416991987979403886768393919473314696421406857084890008516249377944912691716 : Int) - (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int)) - (7219116586605449134138994123065718562687353888322121594704762768593102939856 : Int) + (-8233959624322192335486518158126699282976554433849447299690452822681538400803 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5961268831825485731252199515004800314005407259057680931951253262 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (5961268831825485731252199515004800314005407259057680931951253262 : Nat) = 2980634415912742865626099757502400157002703629528840465975626631 + 2980634415912742865626099757502400157002703629528840465975626631 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep211
