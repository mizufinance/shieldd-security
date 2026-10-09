import ShielddSecurity.ConcretePointTraceStep120
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep121
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48705534063244610064759631108664746030543742969253284874080975800752547122750
def inputY : F := 9891881026777460469533128640819386919201948907094010748863505415786872805842
def doubleX : F := 20188749895620436335543643812449181685703889475670128215066296607655365558242
def doubleY : F := 3933234886865394274785793801926709301810146412220650638850335657117869506191
def doubleSlope : F := 12733440082295370726510479221093620974704292000148315107021047703317467103701
def outX : F := 20188749895620436335543643812449181685703889475670128215066296607655365558242
def outY : F := 3933234886865394274785793801926709301810146412220650638850335657117869506191

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2407737306593104006700346164482836320 : Nat) • base) + ((2407737306593104006700346164482836320 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep120.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (9891881026777460469533128640819386919201948907094010748863505415786872805842 : Int)) * (9591685181890543822355369706832846026103989464909970650497872520534516632322 : Int) =
        (1 : Int) + (3618889104022177718320224050061026941207036330316626460080406425343477576519 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (12733440082295370726510479221093620974704292000148315107021047703317467103701 : Int) * ((2 : Int) * (9891881026777460469533128640819386919201948907094010748863505415786872805842 : Int)) =
        (3 : Int) * (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) + (-40964 : Int) * (-40964 : Int) + (-130917463921775614844973532623665374427600157886313821774513644345426954094024 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) =
        (12733440082295370726510479221093620974704292000148315107021047703317467103701 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) - (48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) + (-3092167257395568692371689483008472574820602881815375155613548616549547556579 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3933234886865394274785793801926709301810146412220650638850335657117869506191 : Int) =
        (12733440082295370726510479221093620974704292000148315107021047703317467103701 : Int) * ((48705534063244610064759631108664746030543742969253284874080975800752547122750 : Int) - (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int)) - (9891881026777460469533128640819386919201948907094010748863505415786872805842 : Int) + (-6924968093417882362811068360823237011486601286779830164439971188083899807275 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4815474613186208013400692328965672640 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4815474613186208013400692328965672640 : Nat) = 2407737306593104006700346164482836320 + 2407737306593104006700346164482836320 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep121
