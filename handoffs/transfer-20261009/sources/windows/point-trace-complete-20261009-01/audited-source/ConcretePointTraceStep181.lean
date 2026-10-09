import ShielddSecurity.ConcretePointTraceStep180
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep181
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48014335250910506609650122023600251861286839797659429155557026589364830311449
def inputY : F := 24877379213436662361660366021259612104203269489146406808559010533597043643226
def doubleX : F := 28001849522585207766373342824886941819777921447563607012500415465115141660056
def doubleY : F := 42724231404024003359570834440145114107396506321853472808075686206927141823351
def doubleSlope : F := 13709215045223906180840832357079943482865285746687220273094762362076277700735
def outX : F := 28001849522585207766373342824886941819777921447563607012500415465115141660056
def outY : F := 42724231404024003359570834440145114107396506321853472808075686206927141823351

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2775932118215358690941799206195771840403511775218733089 : Nat) • base) + ((2775932118215358690941799206195771840403511775218733089 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep180.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24877379213436662361660366021259612104203269489146406808559010533597043643226 : Int)) * (2342701378052354109507010038457416788821981457012429336178147614591849824861 : Int) =
        (1 : Int) + (2222915909041420997081820088110180178387830894847369778592149008307719501667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13709215045223906180840832357079943482865285746687220273094762362076277700735 : Int) * ((2 : Int) * (24877379213436662361660366021259612104203269489146406808559010533597043643226 : Int)) =
        (3 : Int) * (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) + (-40964 : Int) * (-40964 : Int) + (-118888651426962791713381103672073617380336991020562287826638478684839499000455 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) =
        (13709215045223906180840832357079943482865285746687220273094762362076277700735 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) - (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) + (-3584236489397761090579570051336625572219324125509408812504017656184753424703 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (42724231404024003359570834440145114107396506321853472808075686206927141823351 : Int) =
        (13709215045223906180840832357079943482865285746687220273094762362076277700735 : Int) * ((48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) - (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int)) - (24877379213436662361660366021259612104203269489146406808559010533597043643226 : Int) + (-5232209236954451839427125966644792184503356518033834873564895987199221615406 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5551864236430717381883598412391543680807023550437466178 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (5551864236430717381883598412391543680807023550437466178 : Nat) = 2775932118215358690941799206195771840403511775218733089 + 2775932118215358690941799206195771840403511775218733089 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep181
