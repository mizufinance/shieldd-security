import ShielddSecurity.ConcretePointTraceStep149
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep150
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 13893635581100041838529174086803523763978972725418931508683760845156668731886
def inputY : F := 37981386710589963954145812023721280222085172063335852022147403838315281454010
def doubleX : F := 26743128294051169123626303766926877689760850029753659611217365217079061734238
def doubleY : F := 3582510313114024221961480449621450297679357366172301452415825860858443750120
def doubleSlope : F := 41472568282371547698924438208263009603493237505023895150340306549963059468059
def outX : F := 26743128294051169123626303766926877689760850029753659611217365217079061734238
def outY : F := 3582510313114024221961480449621450297679357366172301452415825860858443750120

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1292644123647063360988068956041602343508746370 : Nat) • base) + ((1292644123647063360988068956041602343508746370 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep149.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37981386710589963954145812023721280222085172063335852022147403838315281454010 : Int)) * (28108088841089580098356471340031256809710102097726883097064857438977611381952 : Int) =
        (1 : Int) + (40719609938939962592235232977292104552064321385680021934510317364956837365503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41472568282371547698924438208263009603493237505023895150340306549963059468059 : Int) * ((2 : Int) * (37981386710589963954145812023721280222085172063335852022147403838315281454010 : Int)) =
        (3 : Int) * (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) + (-40964 : Int) * (-40964 : Int) + (49036503539979064861552076542201394959101282833859470643766024661957897144384 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) =
        (41472568282371547698924438208263009603493237505023895150340306549963059468059 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) - (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) + (-32801472545114839357773827642016992303917579106702328155010702075897085384103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3582510313114024221961480449621450297679357366172301452415825860858443750120 : Int) =
        (41472568282371547698924438208263009603493237505023895150340306549963059468059 : Int) * ((13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) - (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int)) - (37981386710589963954145812023721280222085172063335852022147403838315281454010 : Int) + (10162917318570697205892285141408670581488572113919994257598326508586616780146 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2585288247294126721976137912083204687017492740 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2585288247294126721976137912083204687017492740 : Nat) = 1292644123647063360988068956041602343508746370 + 1292644123647063360988068956041602343508746370 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep150
