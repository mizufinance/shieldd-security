import ShielddSecurity.ConcretePointTraceStep076
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep077
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 51224030876542622490619676297094471787311739364320097163168453089175543903435
def inputY : F := 28266505327550710269122515844353560386451419129322240745593377291084516020446
def doubleX : F := 9530522212558258515445842833019539179108131416257255178908986828912756595823
def doubleY : F := 18244361418899087078327179046944438114446479352870520458680288467011164498252
def doubleSlope : F := 21324216821355957621179641547204381043023526293888526363139034032738004305175
def outX : F := 9530522212558258515445842833019539179108131416257255178908986828912756595823
def outY : F := 18244361418899087078327179046944438114446479352870520458680288467011164498252

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((136864020225465538186446 : Nat) • base) + ((136864020225465538186446 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep076.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28266505327550710269122515844353560386451419129322240745593377291084516020446 : Int)) * (20720024020761378398523271072747530231419378357526570318185097646459891487279 : Int) =
        (1 : Int) + (22339006163766988414848112388335986110569647299414522001989405477821664848259 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (21324216821355957621179641547204381043023526293888526363139034032738004305175 : Int) * ((2 : Int) * (28266505327550710269122515844353560386451419129322240745593377291084516020446 : Int)) =
        (3 : Int) * (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) + (-40964 : Int) * (-40964 : Int) + (-127130172209117208364265164680106830620541789753295392658291108044241830726247 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) =
        (21324216821355957621179641547204381043023526293888526363139034032738004305175 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) - (51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) + (-8671967837392084898070263390522034683633021769663518196771569468297625838100 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (18244361418899087078327179046944438114446479352870520458680288467011164498252 : Int) =
        (21324216821355957621179641547204381043023526293888526363139034032738004305175 : Int) * ((51224030876542622490619676297094471787311739364320097163168453089175543903435 : Int) - (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int)) - (28266505327550710269122515844353560386451419129322240745593377291084516020446 : Int) + (-16955594158093425943603921500653080786706629815146244682930193659835511996954 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (273728040450931076372892 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (273728040450931076372892 : Nat) = 136864020225465538186446 + 136864020225465538186446 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep077
