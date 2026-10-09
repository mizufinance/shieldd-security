import ShielddSecurity.ConcretePointTraceStep099
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep100
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 13239922607602991637023780189025675452565898633239401588429543605532877284469
def inputY : F := 36047738064920237178441897142007024680571271339858281647969177837624305380552
def doubleX : F := 20009907507953071182540414653694349699384315542128005004506761726232438594975
def doubleY : F := 7699252430780067967829821748328884041794849636796367412975894730947255241395
def doubleSlope : F := 48009297950507279065568982738759752241182101573353664238728553704907607521703
def outX : F := 20009907507953071182540414653694349699384315542128005004506761726232438594975
def outY : F := 7699252430780067967829821748328884041794849636796367412975894730947255241395

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1148098614975502017355130274049 : Nat) • base) + ((1148098614975502017355130274049 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep099.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36047738064920237178441897142007024680571271339858281647969177837624305380552 : Int)) * (28243494943495531748382742740156633029442962926385375217419280148025016073833 : Int) =
        (1 : Int) + (38832730620427790453813437849246954665457898416579406392694191389422144003087 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (48009297950507279065568982738759752241182101573353664238728553704907607521703 : Int) * ((2 : Int) * (36047738064920237178441897142007024680571271339858281647969177837624305380552 : Int)) =
        (3 : Int) * (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) + (-40964 : Int) * (-40964 : Int) + (55980119195715935374616291482136051062065372186719135420988015836008835181509 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) =
        (48009297950507279065568982738759752241182101573353664238728553704907607521703 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) - (13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) + (-43956407364283789623724077113042020123478570332210038287689748996393243862128 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (7699252430780067967829821748328884041794849636796367412975894730947255241395 : Int) =
        (48009297950507279065568982738759752241182101573353664238728553704907607521703 : Int) * ((13239922607602991637023780189025675452565898633239401588429543605532877284469 : Int) - (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int)) - (36047738064920237178441897142007024680571271339858281647969177837624305380552 : Int) + (6198470438718297064535833665775376316721538331433657270696809850345538804705 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2296197229951004034710260548098 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2296197229951004034710260548098 : Nat) = 1148098614975502017355130274049 + 1148098614975502017355130274049 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep100
