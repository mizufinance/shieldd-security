import ShielddSecurity.ConcretePointTraceStep008
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep009
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25086419878455168332628307760170701926943674741615533051579194352381285095965
def inputY : F := 20495360833676557890588252262014143857305950680061967017112910574000081292885
def doubleX : F := 12537515647106300077041285216198554682667805938571916666641463807023026655468
def doubleY : F := 21885240457150986820414340276483632906168489094755335722954120145310826737205
def doubleSlope : F := 51011777782980070523908806287855842727846492136208692326653040093105576855131
def addX : F := 48582032202577647363196637196511182799156096092606079039550867032120158236127
def addY : F := 14929284027876552358580632858432927529601745590199407635281342990311853652132
def addSlope : F := 37665310559857566838146738722460271472276612489709158458295003699847364656901
def outX : F := 48582032202577647363196637196511182799156096092606079039550867032120158236127
def outY : F := 14929284027876552358580632858432927529601745590199407635281342990311853652132

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((463 : Nat) • base) + ((463 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep008.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (20495360833676557890588252262014143857305950680061967017112910574000081292885 : Int)) * (44239014766896442308640401164197984269638790127171132839059481298730574082426 : Int) =
        (1 : Int) + (34582986077592675609424062503343092520134501925126068155551647906187557384963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (51011777782980070523908806287855842727846492136208692326653040093105576855131 : Int) * ((2 : Int) * (20495360833676557890588252262014143857305950680061967017112910574000081292885 : Int)) =
        (3 : Int) * (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) + (-40964 : Int) * (-40964 : Int) + (3871856762693252880485747814419812509413488490062099906151776226528938629203 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int) =
        (51011777782980070523908806287855842727846492136208692326653040093105576855131 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) - (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) + (-49626357219923654020842462697856949671636387062483366769682173858681041526587 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21885240457150986820414340276483632906168489094755335722954120145310826737205 : Int) =
        (51011777782980070523908806287855842727846492136208692326653040093105576855131 : Int) * ((25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) - (12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int)) - (20495360833676557890588252262014143857305950680061967017112910574000081292885 : Int) + (-12208090585529666462967913257329854363965217874277629036427298182757685603809 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((463 : Nat) • base) + ((463 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (19105108542536958529897969493744742798390375123163740048179799217284473374099 : Int) =
        (1 : Int) + (-9889491644191122195276468327111442976206803959022390941316817220111642213222 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (37665310559857566838146738722460271472276612489709158458295003699847364656901 : Int) * ((12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (21885240457150986820414340276483632906168489094755335722954120145310826737205 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-19496920063460271147680127229676436991288820698921664797368006143541469768398 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int) =
        (37665310559857566838146738722460271472276612489709158458295003699847364656901 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-27055438949619930630571515257867864294381451041445857213071573730609101066307 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (14929284027876552358580632858432927529601745590199407635281342990311853652132 : Int) =
        (37665310559857566838146738722460271472276612489709158458295003699847364656901 : Int) * ((12537515647106300077041285216198554682667805938571916666641463807023026655468 : Int) - (48582032202577647363196637196511182799156096092606079039550867032120158236127 : Int)) - (21885240457150986820414340276483632906168489094755335722954120145310826737205 : Int) + (25891203408115684318463126011860472605090213086916301787754307867838892426392 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (927 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (927 : Nat) = 463 + 463 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
#check @addX
#print axioms addX

set_option pp.all true in
#check @addY
#print axioms addY

set_option pp.all true in
#check @addSlope
#print axioms addSlope

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
#check @next_add
#print axioms next_add

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep009
