import ShielddSecurity.ConcretePointTraceStep075
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep076
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18369007307486640951331358086771155548306762551965108385660059200984724505382
def inputY : F := 12781459219896037092697101469326479412916386723360669015776463758550304921586
def doubleX : F := 51224030876542622490619676297094471787311739364320097163168453089175543903435
def doubleY : F := 28266505327550710269122515844353560386451419129322240745593377291084516020446
def doubleSlope : F := 49528200222002579859998784366284435928210564293520654982290542111148329189305
def outX : F := 51224030876542622490619676297094471787311739364320097163168453089175543903435
def outY : F := 28266505327550710269122515844353560386451419129322240745593377291084516020446

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((68432010112732769093223 : Nat) • base) + ((68432010112732769093223 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep075.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (12781459219896037092697101469326479412916386723360669015776463758550304921586 : Int)) * (13654051608836790595823508934999140324008947681572457026900631055920497683381 : Int) =
        (1 : Int) + (6656461944874302354861173583134090368997339342330682667831720435467433486387 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49528200222002579859998784366284435928210564293520654982290542111148329189305 : Int) * ((2 : Int) * (12781459219896037092697101469326479412916386723360669015776463758550304921586 : Int)) =
        (3 : Int) * (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) + (-40964 : Int) * (-40964 : Int) + (4840656392394044988104107043550891342223106590487954350831820334534870510888 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) =
        (49528200222002579859998784366284435928210564293520654982290542111148329189305 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) - (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) + (-46781761704902696667733789388308317699573669458149601015155306932614565451938 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (28266505327550710269122515844353560386451419129322240745593377291084516020446 : Int) =
        (49528200222002579859998784366284435928210564293520654982290542111148329189305 : Int) * ((18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) - (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int)) - (12781459219896037092697101469326479412916386723360669015776463758550304921586 : Int) + (31033146299019550424723646424839264578661956715902472037596840386689567302669 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (136864020225465538186446 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (136864020225465538186446 : Nat) = 68432010112732769093223 + 68432010112732769093223 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep076
