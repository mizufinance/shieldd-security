import ShielddSecurity.ConcretePointTraceStep193
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep194
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28351713828157723238237498368422776453633195243955962703556456885277541961457
def inputY : F := 1910096758335463814148690304927784567117063602611275147333593907816339921721
def doubleX : F := 2322766695851259706803292603981978373994265966127514915737537875644698136034
def doubleY : F := 24781857657920565755633633570950856395321146453385061297553991836686256725556
def doubleSlope : F := 16668609699068020483136809428471306683135258391601630200987640060666974496760
def outX : F := 2322766695851259706803292603981978373994265966127514915737537875644698136034
def outY : F := 24781857657920565755633633570950856395321146453385061297553991836686256725556

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((22740435912420218396195219097155762916585568462591861465268 : Nat) • base) + ((22740435912420218396195219097155762916585568462591861465268 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep193.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1910096758335463814148690304927784567117063602611275147333593907816339921721 : Int)) * (13828519254288951665920793475764579757297089246502312856853172365137714287272 : Int) =
        (1 : Int) + (1007470923751328629022637913524401881748697464687044710924791266231976574671 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16668609699068020483136809428471306683135258391601630200987640060666974496760 : Int) * ((2 : Int) * (1910096758335463814148690304927784567117063602611275147333593907816339921721 : Int)) =
        (3 : Int) * (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) + (-40964 : Int) * (-40964 : Int) + (-44774340247698587136462847391679380787913122000521667957858333137990368604467 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int) =
        (16668609699068020483136809428471306683135258391601630200987640060666974496760 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) - (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) + (-5298711013631820010671332892347908022899191610144601424073239122686173713540 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24781857657920565755633633570950856395321146453385061297553991836686256725556 : Int) =
        (16668609699068020483136809428471306683135258391601630200987640060666974496760 : Int) * ((28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) - (2322766695851259706803292603981978373994265966127514915737537875644698136034 : Int)) - (1910096758335463814148690304927784567117063602611275147333593907816339921721 : Int) + (-8274227505063247513232953998519327677239885624514468647289685212778270447131 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (45480871824840436792390438194311525833171136925183722930536 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (45480871824840436792390438194311525833171136925183722930536 : Nat) = 22740435912420218396195219097155762916585568462591861465268 + 22740435912420218396195219097155762916585568462591861465268 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep194
