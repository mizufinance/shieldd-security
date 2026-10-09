import ShielddSecurity.ConcretePointTraceStep142
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep143
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 36619481870374698177242339535765999636530294886257028529188103025204578161488
def inputY : F := 37608226641050498246563775203336926750468533856932426711139792756585177220237
def doubleX : F := 30587028541489315436923749089162205017728965372456373683571427986941776893865
def doubleY : F := 1404480771254171368937995122912530319389805155987308049282722847233343187735
def doubleSlope : F := 46349250022333405724082642378393948999090566257110902524811869973174090219246
def outX : F := 30587028541489315436923749089162205017728965372456373683571427986941776893865
def outY : F := 1404480771254171368937995122912530319389805155987308049282722847233343187735

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((10098782215992682507719288719075018308662081 : Nat) • base) + ((10098782215992682507719288719075018308662081 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep142.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37608226641050498246563775203336926750468533856932426711139792756585177220237 : Int)) * (26015602716660977425656539067338234339977173972058237550463386182664383114676 : Int) =
        (1 : Int) + (37317988110393372516045898370291147198094109227808007681085223496215374592071 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (46349250022333405724082642378393948999090566257110902524811869973174090219246 : Int) * ((2 : Int) * (37608226641050498246563775203336926750468533856932426711139792756585177220237 : Int)) =
        (3 : Int) * (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) + (-40964 : Int) * (-40964 : Int) + (-10235991229406475615752622125772641987456722950614781722365670252410256880612 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) =
        (46349250022333405724082642378393948999090566257110902524811869973174090219246 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) - (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) + (-40969145083552108271872633130817143120425158171361076053339717166812402263811 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1404480771254171368937995122912530319389805155987308049282722847233343187735 : Int) =
        (46349250022333405724082642378393948999090566257110902524811869973174090219246 : Int) * ((36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) - (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int)) - (37608226641050498246563775203336926750468533856932426711139792756585177220237 : Int) + (-5332221244610764296772753655398002908843622428474961066185951507430692485022 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (20197564431985365015438577438150036617324162 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (20197564431985365015438577438150036617324162 : Nat) = 10098782215992682507719288719075018308662081 + 10098782215992682507719288719075018308662081 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep143
