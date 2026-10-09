import ShielddSecurity.ConcretePointTraceStep175
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep176
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26676143068213058137815775796005897050710670109559509647531094584251080299120
def inputY : F := 50408293294553225393996623042617029869269350007292622811372669154651582664045
def doubleX : F := 28775296852505744947996206910410988101402576837126816807998287590104983744432
def doubleY : F := 27492392060764410741441622795304753493806197639329667585137468569762792367114
def doubleSlope : F := 41330219683361956500388641818448270129058094002888904919769923832311228130372
def outX : F := 28775296852505744947996206910410988101402576837126816807998287590104983744432
def outY : F := 27492392060764410741441622795304753493806197639329667585137468569762792367114

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((86747878694229959091931225193617870012609742975585409 : Nat) • base) + ((86747878694229959091931225193617870012609742975585409 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep175.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (50408293294553225393996623042617029869269350007292622811372669154651582664045 : Int)) * (21814769281607001043379788615456097791229182733430750936032753009403600987167 : Int) =
        (1 : Int) + (41942478672383844762357110407090452848295286267277347150986774226595473221733 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41330219683361956500388641818448270129058094002888904919769923832311228130372 : Int) * ((2 : Int) * (50408293294553225393996623042617029869269350007292622811372669154651582664045 : Int)) =
        (3 : Int) * (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) + (-40964 : Int) * (-40964 : Int) + (38750604193806092094310444527264066624265957385415389681241497282764169256408 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) =
        (41330219683361956500388641818448270129058094002888904919769923832311228130372 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) - (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) + (-32576686350135839726132569304362264242940162044657427433778843285782190497160 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27492392060764410741441622795304753493806197639329667585137468569762792367114 : Int) =
        (41330219683361956500388641818448270129058094002888904919769923832311228130372 : Int) * ((26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) - (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int)) - (50408293294553225393996623042617029869269350007292622811372669154651582664045 : Int) + (1654563536209130370955097051817969464684773207305763677139284360448777303671 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (173495757388459918183862450387235740025219485951170818 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (173495757388459918183862450387235740025219485951170818 : Nat) = 86747878694229959091931225193617870012609742975585409 + 86747878694229959091931225193617870012609742975585409 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep176
