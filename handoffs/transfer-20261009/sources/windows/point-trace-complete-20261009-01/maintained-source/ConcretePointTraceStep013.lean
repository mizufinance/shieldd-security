import ShielddSecurity.ConcretePointTraceStep012
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep013
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9615612681959853836191120892692185353859817150479829011104681583320823510738
def inputY : F := 42327772510509623778676028940091341497326703384054299441788045192093919904545
def doubleX : F := 44458785688534054192797513222025200578002196316154071113948646250915212113101
def doubleY : F := 46054047493182044412507592300112323905490616910150683491789173610876730800645
def doubleSlope : F := 11530055147922762021672163297821530138780404244938766413648324739403012678887
def outX : F := 44458785688534054192797513222025200578002196316154071113948646250915212113101
def outY : F := 46054047493182044412507592300112323905490616910150683491789173610876730800645

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((7419 : Nat) • base) + ((7419 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep012.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42327772510509623778676028940091341497326703384054299441788045192093919904545 : Int)) * (34280243101396388313887002230585354064301484909727494321445644215240450227945 : Int) =
        (1 : Int) + (55344030275256343904499180435287470284542206095920081476260097783768292896273 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (11530055147922762021672163297821530138780404244938766413648324739403012678887 : Int) * ((2 : Int) * (42327772510509623778676028940091341497326703384054299441788045192093919904545 : Int)) =
        (3 : Int) * (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) + (-40964 : Int) * (-40964 : Int) + (13324905488615736154555097337487794194350684032531341429520980559385293262290 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) =
        (11530055147922762021672163297821530138780404244938766413648324739403012678887 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) - (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) + (-2535328556453720928643383719863333801945256087857909260829454296314548250120 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (46054047493182044412507592300112323905490616910150683491789173610876730800645 : Int) =
        (11530055147922762021672163297821530138780404244938766413648324739403012678887 : Int) * ((9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) - (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int)) - (42327772510509623778676028940091341497326703384054299441788045192093919904545 : Int) + (7661619167271721941428511874507647510656107960823449017622812386957338965667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (14838 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (14838 : Nat) = 7419 + 7419 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep013
