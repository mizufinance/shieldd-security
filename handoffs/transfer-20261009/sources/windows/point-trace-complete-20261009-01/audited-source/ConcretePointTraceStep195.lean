import ShielddSecurity.ConcretePointTraceStep194
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep195
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 2322766695851259706803292603981978373994265966127514915737537875644698136034
def inputY : F := 24781857657920565755633633570950856395321146453385061297553991836686256725556
def doubleX : F := 45291916205121456350242883724662810644790040143665673920277142435155623198101
def doubleY : F := 41003502079105349511337519576762210108166022459189333537549067628848645574648
def doubleSlope : F := 19317321318502121015476715230690755399567873719702657705068578378422064771746
def outX : F := 45291916205121456350242883724662810644790040143665673920277142435155623198101
def outY : F := 41003502079105349511337519576762210108166022459189333537549067628848645574648

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((45480871824840436792390438194311525833171136925183722930536 : Nat) • base) + ((45480871824840436792390438194311525833171136925183722930536 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep194.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24781857657920565755633633570950856395321146453385061297553991836686256725556 : Int)) * (22258406308214949483153166583580031378824967647678587442366700498810719085417 : Int) =
        (1 : Int) + (21039208556359013819618425039807658949529068253816611610072890336630708862631 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19317321318502121015476715230690755399567873719702657705068578378422064771746 : Int) * ((2 : Int) * (24781857657920565755633633570950856395321146453385061297553991836686256725556 : Int)) =
        (3 : Int) * (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) + (-40964 : Int) * (-40964 : Int) + (17950543897306763182418114550721962534292291352318289224961925856130452829524 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) =
        (19317321318502121015476715230690755399567873719702657705068578378422064771746 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) - (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) + (-7116480876422379479879521759008538766815334687508211550795499742003258037555 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (41003502079105349511337519576762210108166022459189333537549067628848645574648 : Int) =
        (19317321318502121015476715230690755399567873719702657705068578378422064771746 : Int) * ((2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) - (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int)) - (24781857657920565755633633570950856395321146453385061297553991836686256725556 : Int) + (15829789530185572086196466714361725203594521508894329453030298686470446142322 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (90961743649680873584780876388623051666342273850367445861072 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (90961743649680873584780876388623051666342273850367445861072 : Nat) = 45480871824840436792390438194311525833171136925183722930536 + 45480871824840436792390438194311525833171136925183722930536 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep195
