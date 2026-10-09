import ShielddSecurity.ConcretePointTraceStep056
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep057
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 19335923905674262999057160929532315590043339984859945221466128014705795328784
def inputY : F := 50877486256830705277735530352327310548382597972553854693908769095627960436820
def doubleX : F := 23229236759624610526295678402042587186482520209982066668198783466454158179698
def doubleY : F := 3406172924223861995638869373785609199177078749959398644831399006410667753524
def doubleSlope : F := 2288413596073980947240528590585856384803036471237317250261615079329088218965
def outX : F := 23229236759624610526295678402042587186482520209982066668198783466454158179698
def outY : F := 3406172924223861995638869373785609199177078749959398644831399006410667753524

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((130523700929132021 : Nat) • base) + ((130523700929132021 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep056.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (50877486256830705277735530352327310548382597972553854693908769095627960436820 : Int)) * (18783392341334554291759624369670636210669571405142571511625583624826184721696 : Int) =
        (1 : Int) + (36450303633197939436618371449053696606867296678859172468982193033422421122303 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (2288413596073980947240528590585856384803036471237317250261615079329088218965 : Int) * ((2 : Int) * (50877486256830705277735530352327310548382597972553854693908769095627960436820 : Int)) =
        (3 : Int) * (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) + (-40964 : Int) * (-40964 : Int) + (-16949777119602360826178286847099548829455079381595699489457936538582659486280 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) =
        (2288413596073980947240528590585856384803036471237317250261615079329088218965 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) - (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) + (-99871257401658242184021635181636863520200370489328919074312358508852309679 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3406172924223861995638869373785609199177078749959398644831399006410667753524 : Int) =
        (2288413596073980947240528590585856384803036471237317250261615079329088218965 : Int) * ((19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) - (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int)) - (50877486256830705277735530352327310548382597972553854693908769095627960436820 : Int) + (169912489092504733323235393518336637925659545602618436659542132257227690258 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (261047401858264042 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (261047401858264042 : Nat) = 130523700929132021 + 130523700929132021 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep057
