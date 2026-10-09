import ShielddSecurity.ConcretePointTraceStep009
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep010
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48582032202577647363196637196511182799156096092606079039550867032120158236127
def inputY : F := 14929284027876552358580632858432927529601745590199407635281342990311853652132
def doubleX : F := 22442234978684825731632329529465228058157583984752797698598611937614349975524
def doubleY : F := 21746960631068035749333477086487225234479290840653100761459625256678398636989
def doubleSlope : F := 35989187359897437707229580799486468656814219058081455900797100265561895137839
def outX : F := 22442234978684825731632329529465228058157583984752797698598611937614349975524
def outY : F := 21746960631068035749333477086487225234479290840653100761459625256678398636989

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((927 : Nat) • base) + ((927 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep009.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (14929284027876552358580632858432927529601745590199407635281342990311853652132 : Int)) * (31374357743128466287442263377409540624724494174376556349173228850274429533746 : Int) =
        (1 : Int) + (17865505109813230830856247914095514170199385516960561549101795341789368324111 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (35989187359897437707229580799486468656814219058081455900797100265561895137839 : Int) * ((2 : Int) * (14929284027876552358580632858432927529601745590199407635281342990311853652132 : Int)) =
        (3 : Int) * (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) + (-40964 : Int) * (-40964 : Int) + (-114540969110957030479978444846030150575495599252879311118822195241783425744555 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) =
        (35989187359897437707229580799486468656814219058081455900797100265561895137839 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) - (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) + (-24701058244951557902095069553362616987025339313478197476159398372830810179847 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21746960631068035749333477086487225234479290840653100761459625256678398636989 : Int) =
        (35989187359897437707229580799486468656814219058081455900797100265561895137839 : Int) * ((48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) - (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int)) - (14929284027876552358580632858432927529601745590199407635281342990311853652132 : Int) + (-17940962302974314571203803778812160372258878204728667575029183540304651930292 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1854 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1854 : Nat) = 927 + 927 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep010
