import ShielddSecurity.ConcretePointTraceStep126
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep127
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45711149844443227643209881894737829911885535237635519440527627021383646636483
def inputY : F := 286637060483921093632836507847867219039319371102541499388036744422424422876
def doubleX : F := 5566504998693056018120894468442780266711582254133704871534628739920391741905
def doubleY : F := 38165601816628144877808208430799056635264752371660204897234346514679087085370
def doubleSlope : F := 49197645986217364614705642725222169317831633389287010056435186198453112021861
def outX : F := 5566504998693056018120894468442780266711582254133704871534628739920391741905
def outY : F := 38165601816628144877808208430799056635264752371660204897234346514679087085370

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((154095187621958656428822154526901524485 : Nat) • base) + ((154095187621958656428822154526901524485 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep126.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (286637060483921093632836507847867219039319371102541499388036744422424422876 : Int)) * (7709747993700780383091985998090955180528519871673160946416053407296821057803 : Int) =
        (1 : Int) + (84289601140651949340529357851380823809858593298490796119219237189564207335 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49197645986217364614705642725222169317831633389287010056435186198453112021861 : Int) * ((2 : Int) * (286637060483921093632836507847867219039319371102541499388036744422424422876 : Int)) =
        (3 : Int) * (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) + (-40964 : Int) * (-40964 : Int) + (-119008673016431116211592599288959593685410779676997281346861444576065170396131 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) =
        (49197645986217364614705642725222169317831633389287010056435186198453112021861 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) - (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) + (-46159396834732904608315175075056877376319038556481360385714441214219428302986 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (38165601816628144877808208430799056635264752371660204897234346514679087085370 : Int) =
        (49197645986217364614705642725222169317831633389287010056435186198453112021861 : Int) * ((45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) - (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int)) - (286637060483921093632836507847867219039319371102541499388036744422424422876 : Int) + (-37665472708664283706399099689119992518604397603728596691100478326261855098724 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (308190375243917312857644309053803048970 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (308190375243917312857644309053803048970 : Nat) = 154095187621958656428822154526901524485 + 154095187621958656428822154526901524485 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep127
