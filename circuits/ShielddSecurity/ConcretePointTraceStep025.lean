import ShielddSecurity.ConcretePointTraceStep024
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep025
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28442401694150067458265733757665598455697307560125449373022757812391278344207
def inputY : F := 21729355077556603154525861846401546431809362299478912316963800624137387276328
def doubleX : F := 3282269324988528325038993226636785597530619733789972828218290262497888718808
def doubleY : F := 30852909997361908207513808641016876165434383588893462061390256803927125673339
def doubleSlope : F := 336610836218815187029807358352628620373448371001096397555143137790015864662
def outX : F := 3282269324988528325038993226636785597530619733789972828218290262497888718808
def outY : F := 30852909997361908207513808641016876165434383588893462061390256803927125673339

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((30389917 : Nat) • base) + ((30389917 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep024.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21729355077556603154525861846401546431809362299478912316963800624137387276328 : Int)) * (38592453269135910818407981454966594091681361557303806736254153889003023907080 : Int) =
        (1 : Int) + (31985319882554862342863572957786400286388431749836863233013509640782810272383 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (336610836218815187029807358352628620373448371001096397555143137790015864662 : Int) * ((2 : Int) * (21729355077556603154525861846401546431809362299478912316963800624137387276328 : Int)) =
        (3 : Int) * (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) + (-40964 : Int) * (-40964 : Int) + (-46004418951172064440670571100059748708015806373996910422979145339110322587363 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) =
        (336610836218815187029807358352628620373448371001096397555143137790015864662 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) - (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) + (-2160865145885444668947465769126581807899690896836596367980490398127223030 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30852909997361908207513808641016876165434383588893462061390256803927125673339 : Int) =
        (336610836218815187029807358352628620373448371001096397555143137790015864662 : Int) * ((28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) - (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int)) - (21729355077556603154525861846401546431809362299478912316963800624137387276328 : Int) + (-161514863018383172027084125099579097722117929602972404824250689666508983767 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (60779834 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (60779834 : Nat) = 30389917 + 30389917 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep025
