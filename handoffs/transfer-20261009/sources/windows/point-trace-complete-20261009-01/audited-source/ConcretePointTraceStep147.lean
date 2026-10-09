import ShielddSecurity.ConcretePointTraceStep146
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep147
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39651586123580376443048613161615770209033490101544976781278983951114780125655
def inputY : F := 29990184430001635833391747276110256695705902600559755346520651178972125854927
def doubleX : F := 3623301025167337499878569733857069475992406992412737668849808865328299930740
def doubleY : F := 43979398470855163907982139051870234426029612511068740011282119168703488597491
def doubleSlope : F := 25706424093441685292375723706114641817797519062214458192447531106962900840853
def outX : F := 3623301025167337499878569733857069475992406992412737668849808865328299930740
def outY : F := 43979398470855163907982139051870234426029612511068740011282119168703488597491

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((161580515455882920123508619505200292938593296 : Nat) • base) + ((161580515455882920123508619505200292938593296 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep146.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29990184430001635833391747276110256695705902600559755346520651178972125854927 : Int)) * (15116052077380712997193947280939289472888139854163625646013409645097262794684 : Int) =
        (1 : Int) + (17290955405630491204140033332231249129076993493076501066866409942537856229895 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25706424093441685292375723706114641817797519062214458192447531106962900840853 : Int) * ((2 : Int) * (29990184430001635833391747276110256695705902600559755346520651178972125854927 : Int)) =
        (3 : Int) * (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) + (-40964 : Int) * (-40964 : Int) + (-60547555210003941235217968692391688248764099165620249031370966043073569002333 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) =
        (25706424093441685292375723706114641817797519062214458192447531106962900840853 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) - (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) + (-12602445128737929240428433660241845060668945529428025053712697277327793182879 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43979398470855163907982139051870234426029612511068740011282119168703488597491 : Int) =
        (25706424093441685292375723706114641817797519062214458192447531106962900840853 : Int) * ((39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) - (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int)) - (29990184430001635833391747276110256695705902600559755346520651178972125854927 : Int) + (-17662685575591751744428160793731270391069351972916266439332341087298918558429 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (323161030911765840247017239010400585877186592 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (323161030911765840247017239010400585877186592 : Nat) = 161580515455882920123508619505200292938593296 + 161580515455882920123508619505200292938593296 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep147
