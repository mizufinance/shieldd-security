import ShielddSecurity.ConcretePointTraceStep245
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep246
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 17412479571858371534042690312005737690661713604938955644290724622446329649486
def inputY : F := 2613041481024350157144950501103978605865691775397781942176600163096662847833
def doubleX : F := 5362276510488518410871535808777810374046480688426836866761034374813066805102
def doubleY : F := 3592466589430162956169247054654401568491443923860061269690435077416125867196
def doubleSlope : F := 17108437966125132817260009843946160346235360526058976411119988679851531620932
def addX : F := 30668999562863422133654530863737643728013407069103903704350978704685986499942
def addY : F := 29412669514748492492094067424516849589830800333394186345669559416848434687098
def addSlope : F := 7081954314007297186052280681941664396739827232381627003897127041106953068705
def outX : F := 30668999562863422133654530863737643728013407069103903704350978704685986499942
def outY : F := 29412669514748492492094067424516849589830800333394186345669559416848434687098

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) • base) + ((102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep245.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2613041481024350157144950501103978605865691775397781942176600163096662847833 : Int)) * (2311242008294129643749286343437665660325840492612348651114309003788495672657 : Int) =
        (1 : Int) + (230352643879336252871992484711518246391654104795894389046566782863885423697 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (17108437966125132817260009843946160346235360526058976411119988679851531620932 : Int) * ((2 : Int) * (2613041481024350157144950501103978605865691775397781942176600163096662847833 : Int)) =
        (3 : Int) * (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) + (-40964 : Int) * (-40964 : Int) + (-15641451880413814692013686113670407967696771058222287911811288029180449401652 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int) =
        (17108437966125132817260009843946160346235360526058976411119988679851531620932 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) - (17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) + (-5582030406914963294419402774388194524314007074007007815998979857085497372686 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3592466589430162956169247054654401568491443923860061269690435077416125867196 : Int) =
        (17108437966125132817260009843946160346235360526058976411119988679851531620932 : Int) * ((17412479571858371534042690312005737690661713604938955644290724622446329649486 : Int) - (5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int)) - (2613041481024350157144950501103978605865691775397781942176600163096662847833 : Int) + (-3931662261116463965878158624923022301511013901169420592787496215624259553643 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) • base) + ((102413818701418340780171368180050714526655019779254957521333736912377863346 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34055614862731184061432871882504377397346614929104532378492862478106386474324 : Int) =
        (1 : Int) + (-22288526151034938531216891894847487565952676693235101333910466115741691894565 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (7081954314007297186052280681941664396739827232381627003897127041106953068705 : Int) * ((5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (3592466589430162956169247054654401568491443923860061269690435077416125867196 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4634957394380382074155256740102281188766621083143405281387876847000846542935 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) =
        (7081954314007297186052280681941664396739827232381627003897127041106953068705 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-956484024309333330296119612705954889945287660324639003871451595596912816482 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (29412669514748492492094067424516849589830800333394186345669559416848434687098 : Int) =
        (7081954314007297186052280681941664396739827232381627003897127041106953068705 : Int) * ((5362276510488518410871535808777810374046480688426836866761034374813066805102 : Int) - (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int)) - (3592466589430162956169247054654401568491443923860061269690435077416125867196 : Int) + (3417909129876996615601475450793770216957181803300771308556589188555035925038 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) = 102413818701418340780171368180050714526655019779254957521333736912377863346 + 102413818701418340780171368180050714526655019779254957521333736912377863346 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep246
