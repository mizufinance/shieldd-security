import ShielddSecurity.ConcretePointTraceStep244
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep245
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 33652555203852847325435703373215766219990032473577316466385438734209534304630
def inputY : F := 29383556134240677589933676479674591580917833333552622040359156512591692573028
def doubleX : F := 17412479571858371534042690312005737690661713604938955644290724622446329649486
def doubleY : F := 2613041481024350157144950501103978605865691775397781942176600163096662847833
def doubleSlope : F := 41744629531164445416851754367138043930800142614978084587269802590140311259134
def outX : F := 17412479571858371534042690312005737690661713604938955644290724622446329649486
def outY : F := 2613041481024350157144950501103978605865691775397781942176600163096662847833

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((51206909350709170390085684090025357263327509889627478760666868456188931673 : Nat) • base) + ((51206909350709170390085684090025357263327509889627478760666868456188931673 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep244.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29383556134240677589933676479674591580917833333552622040359156512591692573028 : Int)) * (39546517228139718087130847284155158762707304964033033069284490774973633882067 : Int) =
        (1 : Int) + (44321461404270839579161039746975303016854737632980214866093402598809511834327 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41744629531164445416851754367138043930800142614978084587269802590140311259134 : Int) * ((2 : Int) * (29383556134240677589933676479674591580917833333552622040359156512591692573028 : Int)) =
        (3 : Int) * (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) + (-40964 : Int) * (-40964 : Int) + (-18008130537104446201472750338634887914934855136844254882179001380137850844524 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) =
        (41744629531164445416851754367138043930800142614978084587269802590140311259134 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) - (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) + (-33233241342385451799823490818082715569090253142684149747308124483158993175506 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2613041481024350157144950501103978605865691775397781942176600163096662847833 : Int) =
        (41744629531164445416851754367138043930800142614978084587269802590140311259134 : Int) * ((33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) - (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int)) - (29383556134240677589933676479674591580917833333552622040359156512591692573028 : Int) + (-12928857171764925917860211324834700876708051989446915537000579912977882698995 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) = 51206909350709170390085684090025357263327509889627478760666868456188931673 + 51206909350709170390085684090025357263327509889627478760666868456188931673 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep245
