import ShielddSecurity.ConcretePointTraceStep017
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep018
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 49572775152340724237764497713283390171381050695988256822223678367978494173491
def inputY : F := 18389945054155396692988255310000093496342317570943788482869097001183762115676
def doubleX : F := 42439175517686597877430203423179344753576770071956310248333887278347836601768
def doubleY : F := 30451232257171430674781960711121263461066932687361394646452201487527808425633
def doubleSlope : F := 551814407366964868136353993072767656454825960443101539634723777925844643876
def outX : F := 42439175517686597877430203423179344753576770071956310248333887278347836601768
def outY : F := 30451232257171430674781960711121263461066932687361394646452201487527808425633

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((237421 : Nat) • base) + ((237421 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep017.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18389945054155396692988255310000093496342317570943788482869097001183762115676 : Int)) * (38837180229782958159902333959823086483497148579614331681509866116712564042267 : Int) =
        (1 : Int) + (27241410888964725319984184277033445829978980617293810434264766418418332601191 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (551814407366964868136353993072767656454825960443101539634723777925844643876 : Int) * ((2 : Int) * (18389945054155396692988255310000093496342317570943788482869097001183762115676 : Int)) =
        (3 : Int) * (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) + (-40964 : Int) * (-40964 : Int) + (-140210960741969857726705883342070815565001513600699732448643692520872096301947 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int) =
        (551814407366964868136353993072767656454825960443101539634723777925844643876 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) - (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) + (-5807076532255511334923741296781428676180537059617199536775885059599158538 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30451232257171430674781960711121263461066932687361394646452201487527808425633 : Int) =
        (551814407366964868136353993072767656454825960443101539634723777925844643876 : Int) * ((49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) - (42439175517686597877430203423179344753576770071956310248333887278347836601768 : Int)) - (18389945054155396692988255310000093496342317570943788482869097001183762115676 : Int) + (-75071180592350827843843168254127847291445121561394164916973637059647759503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (474842 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (474842 : Nat) = 237421 + 237421 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep018
