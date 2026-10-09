import ShielddSecurity.ConcretePointTraceStep091
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep092
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 13189248768049415015311464690063593091844652137897891178804722554501747703579
def inputY : F := 42343061399669842103949368665569926207927685960764958752636572914557776937678
def doubleX : F := 51173066641752700007264529121140433676795022166350596130073961272919411352843
def doubleY : F := 11732452124096413568853259860659433381095630581913234171290409685136186289477
def doubleSlope : F := 7613092212244887601017165389848256586265327075071722380761915343752444658265
def outX : F := 51173066641752700007264529121140433676795022166350596130073961272919411352843
def outY : F := 11732452124096413568853259860659433381095630581913234171290409685136186289477

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4484760214748054755293477633 : Nat) • base) + ((4484760214748054755293477633 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep091.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42343061399669842103949368665569926207927685960764958752636572914557776937678 : Int)) * (8600678898155018712967327133566540118152274949518595188604573192103811794621 : Int) =
        (1 : Int) + (13890454710525246819697748380581467885732487051550677565033111800922650463275 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (7613092212244887601017165389848256586265327075071722380761915343752444658265 : Int) * ((2 : Int) * (42343061399669842103949368665569926207927685960764958752636572914557776937678 : Int)) =
        (3 : Int) * (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) + (-40964 : Int) * (-40964 : Int) + (2342945785916168367538110137327647741399922844726487452319680635930506868305 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int) =
        (7613092212244887601017165389848256586265327075071722380761915343752444658265 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) - (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) + (-1105334331477652771932761917829366762176696534659309156417369506456799174584 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (11732452124096413568853259860659433381095630581913234171290409685136186289477 : Int) =
        (7613092212244887601017165389848256586265327075071722380761915343752444658265 : Int) * ((13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) - (51173066641752700007264529121140433676795022166350596130073961272919411352843 : Int)) - (42343061399669842103949368665569926207927685960764958752636572914557776937678 : Int) + (5514817995882200455342187023274533049625784492407501163537085083045064884355 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (8969520429496109510586955266 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (8969520429496109510586955266 : Nat) = 4484760214748054755293477633 + 4484760214748054755293477633 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep092
