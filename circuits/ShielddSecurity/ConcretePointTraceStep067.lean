import ShielddSecurity.ConcretePointTraceStep066
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep067
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30239546712992809695573208682375305651971921206300777841516633041370378850264
def inputY : F := 28108137010333261335632345513343544414478736331499131446870039524044997268852
def doubleX : F := 44603938340258233252113140296809445244459209136115965877431219943072728940159
def doubleY : F := 1524216170352971842545121194890977435737332366943269806145652212153043694917
def doubleSlope : F := 43994021061819677924899334439704037806368271747389010153625244225704100446207
def outX : F := 44603938340258233252113140296809445244459209136115965877431219943072728940159
def outY : F := 1524216170352971842545121194890977435737332366943269806145652212153043694917

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((133656269751431189635 : Nat) • base) + ((133656269751431189635 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep066.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28108137010333261335632345513343544414478736331499131446870039524044997268852 : Int)) * (45194228985256487103868127306287309846606580007493025140873974682549601081998 : Int) =
        (1 : Int) + (48452536594509389695131140620961840231773247789741490690997719899273026297007 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (43994021061819677924899334439704037806368271747389010153625244225704100446207 : Int) * ((2 : Int) * (28108137010333261335632345513343544414478736331499131446870039524044997268852 : Int)) =
        (3 : Int) * (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) + (-40964 : Int) * (-40964 : Int) + (-5151255929980638449023176912523338046249426690274276690489458690090906370104 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) =
        (43994021061819677924899334439704037806368271747389010153625244225704100446207 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) - (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) + (-36911253654558185272217156272324325284470965738397793018886132662888861966810 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1524216170352971842545121194890977435737332366943269806145652212153043694917 : Int) =
        (43994021061819677924899334439704037806368271747389010153625244225704100446207 : Int) * ((30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) - (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int)) - (28108137010333261335632345513343544414478736331499131446870039524044997268852 : Int) + (12051812727060494923430815553946283083777576250503768726549406751509957401618 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (267312539502862379270 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (267312539502862379270 : Nat) = 133656269751431189635 + 133656269751431189635 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep067
