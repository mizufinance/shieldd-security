import ShielddSecurity.ConcretePointTraceStep218
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep219
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 42384313743839024571066145945497512904081025300568690508294687983298515134450
def inputY : F := 8389806504398485309950405340320602013882159742298963217211406908110759953067
def doubleX : F := 11345426754867998811639614315686321865344235522776571584934044162566692450284
def doubleY : F := 45289242538100592905525736493705885725582717681764829608109119467416520630401
def doubleSlope : F := 5069047557763254537182344919139982605595927549253594599420031990869117918649
def outX : F := 11345426754867998811639614315686321865344235522776571584934044162566692450284
def outY : F := 45289242538100592905525736493705885725582717681764829608109119467416520630401

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((763042410473662173600281537920614440192692129159383159289760417583 : Nat) • base) + ((763042410473662173600281537920614440192692129159383159289760417583 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep218.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8389806504398485309950405340320602013882159742298963217211406908110759953067 : Int)) * (18268390621234873520096974645314365452458129323998430951981432725042895482935 : Int) =
        (1 : Int) + (5845931318855298470053708723251931736850552615804912398518606228808012645753 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (5069047557763254537182344919139982605595927549253594599420031990869117918649 : Int) * ((2 : Int) * (8389806504398485309950405340320602013882159742298963217211406908110759953067 : Int)) =
        (3 : Int) * (42384313743839024571066145945497512904081025300568690508294687983298515134450 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (42384313743839024571066145945497512904081025300568690508294687983298515134450 : Int) + (-40964 : Int) * (-40964 : Int) + (-101156574207084836327586152904176595017571687311403587908935072844568455039510 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) =
        (5069047557763254537182344919139982605595927549253594599420031990869117918649 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42384313743839024571066145945497512904081025300568690508294687983298515134450 : Int) - (42384313743839024571066145945497512904081025300568690508294687983298515134450 : Int) + (-490031739854598088216849479846426517275183628983432816064044579506869383145 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45289242538100592905525736493705885725582717681764829608109119467416520630401 : Int) =
        (5069047557763254537182344919139982605595927549253594599420031990869117918649 : Int) * ((42384313743839024571066145945497512904081025300568690508294687983298515134450 : Int) - (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int)) - (8389806504398485309950405340320602013882159742298963217211406908110759953067 : Int) + (-3000571531640400275493873730329351337522688338865152131519869536797103261482 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1526084820947324347200563075841228880385384258318766318579520835166 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1526084820947324347200563075841228880385384258318766318579520835166 : Nat) = 763042410473662173600281537920614440192692129159383159289760417583 + 763042410473662173600281537920614440192692129159383159289760417583 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep219
