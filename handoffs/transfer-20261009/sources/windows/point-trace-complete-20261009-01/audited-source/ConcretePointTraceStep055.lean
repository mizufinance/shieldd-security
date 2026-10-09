import ShielddSecurity.ConcretePointTraceStep054
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep055
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 43466706957772582939888966516777287978387987349470947592029547584256902209833
def inputY : F := 37042581758421943488030542698411988275685541495247962775714606686734430163555
def doubleX : F := 31821713574010330538382950101579067928739038575118356086435948515512232693722
def doubleY : F := 21428241172033728239026214104476644721006577958178016165697661930459516900527
def doubleSlope : F := 13786870287351421024891802244883921523883985029172911783361978348141740689091
def outX : F := 31821713574010330538382950101579067928739038575118356086435948515512232693722
def outY : F := 21428241172033728239026214104476644721006577958178016165697661930459516900527

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((32630925232283005 : Nat) • base) + ((32630925232283005 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep054.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37042581758421943488030542698411988275685541495247962775714606686734430163555 : Int)) * (4536746451069199733775944323289266448738131511105948286170301733205112789464 : Int) =
        (1 : Int) + (6409840620365196292172607274762342958202231982070265358592109183239790943503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13786870287351421024891802244883921523883985029172911783361978348141740689091 : Int) * ((2 : Int) * (37042581758421943488030542698411988275685541495247962775714606686734430163555 : Int)) =
        (3 : Int) * (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) + (-40964 : Int) * (-40964 : Int) + (-88616072223753008408458938040234539418136358407710366006098253100760707371105 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) =
        (13786870287351421024891802244883921523883985029172911783361978348141740689091 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) - (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) + (-3624956991476323146560458109793281339389655111128198713497730397340293162597 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21428241172033728239026214104476644721006577958178016165697661930459516900527 : Int) =
        (13786870287351421024891802244883921523883985029172911783361978348141740689091 : Int) * ((43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) - (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int)) - (37042581758421943488030542698411988275685541495247962775714606686734430163555 : Int) + (-3061797152098535785823329457194613517681724570151841363862228215281367015963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (65261850464566010 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (65261850464566010 : Nat) = 32630925232283005 + 32630925232283005 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep055
