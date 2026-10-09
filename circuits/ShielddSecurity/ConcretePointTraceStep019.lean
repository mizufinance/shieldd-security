import ShielddSecurity.ConcretePointTraceStep018
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep019
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 42439175517686597877430203423179344753576770071956310248333887278347836601768
def inputY : F := 30451232257171430674781960711121263461066932687361394646452201487527808425633
def doubleX : F := 49056106695774809107938619486548960382363112656046507238744502358430440494009
def doubleY : F := 8925631949118034708956953249085150013483980153936577528223624562751192356671
def doubleSlope : F := 26075296273275209968138734262036640060884919303852219511702094077333349884388
def outX : F := 49056106695774809107938619486548960382363112656046507238744502358430440494009
def outY : F := 8925631949118034708956953249085150013483980153936577528223624562751192356671

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((474842 : Nat) • base) + ((474842 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep018.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (30451232257171430674781960711121263461066932687361394646452201487527808425633 : Int)) * (21090826923299457070147010190973268868966016430649876959803047468081418244513 : Int) =
        (1 : Int) + (24496269662410588675352561324135831591285228856754683107969800746468386498689 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (26075296273275209968138734262036640060884919303852219511702094077333349884388 : Int) * ((2 : Int) * (30451232257171430674781960711121263461066932687361394646452201487527808425633 : Int)) =
        (3 : Int) * (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) + (-40964 : Int) * (-40964 : Int) + (-72759366314318923096281749767941129715701561293436089996188528323481676550024 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) =
        (26075296273275209968138734262036640060884919303852219511702094077333349884388 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) - (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) + (-12966715506669213848883327490787947872686414981600993947323911821539002143759 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (8925631949118034708956953249085150013483980153936577528223624562751192356671 : Int) =
        (26075296273275209968138734262036640060884919303852219511702094077333349884388 : Int) * ((42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) - (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int)) - (30451232257171430674781960711121263461066932687361394646452201487527808425633 : Int) + (3290465550775597473516414004729404790858630333586014776815851852836962987524 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (949684 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (949684 : Nat) = 474842 + 474842 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep019
