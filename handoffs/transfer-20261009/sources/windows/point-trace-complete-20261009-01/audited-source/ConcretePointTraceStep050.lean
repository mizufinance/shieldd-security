import ShielddSecurity.ConcretePointTraceStep049
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep050
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20913556524983791022230689091847888476849531022843889115802912294324893617294
def inputY : F := 49968519463943887879853582934281343552674315037296074161330315232503280538420
def doubleX : F := 36928369294575148816319232585394327370414037357207802071775198350103689751031
def doubleY : F := 30251270830115116985930096146004015737257977999681908728532943911315493970531
def doubleSlope : F := 383985829469890623583779486127202872723474787050383676340445917449694102778
def addX : F := 12946495741151266744237999923232381793408019015383148716798748428561357225791
def addY : F := 15500199270983955706652284227911074337502088724272782586135594828494004060240
def addSlope : F := 26196891745479662166018536910674742527096560535262468254240532052418451808736
def outX : F := 12946495741151266744237999923232381793408019015383148716798748428561357225791
def outY : F := 15500199270983955706652284227911074337502088724272782586135594828494004060240

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1019716413508843 : Nat) • base) + ((1019716413508843 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep049.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (49968519463943887879853582934281343552674315037296074161330315232503280538420 : Int)) * (14036073500348379688398594853002207039440099587647938337236307372144124531483 : Int) =
        (1 : Int) + (26751219830205385821325874050321153334164015606164056806352856928516721263863 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (383985829469890623583779486127202872723474787050383676340445917449694102778 : Int) * ((2 : Int) * (49968519463943887879853582934281343552674315037296074161330315232503280538420 : Int)) =
        (3 : Int) * (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) + (-40964 : Int) * (-40964 : Int) + (-24291692062533047748168690019929934587372050155037881214609646895070454673900 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int) =
        (383985829469890623583779486127202872723474787050383676340445917449694102778 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) - (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) + (-2811912964954629191957093901761985629377078303257373261520423783094518041 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30251270830115116985930096146004015737257977999681908728532943911315493970531 : Int) =
        (383985829469890623583779486127202872723474787050383676340445917449694102778 : Int) * ((20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) - (36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int)) - (49968519463943887879853582934281343552674315037296074161330315232503280538420 : Int) + (117275837288849728415815332284746413865278963493560668695088273188099068449 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1019716413508843 : Nat) • base) + ((1019716413508843 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (13698271502492069689859089384828056395806981630705116581298389269113523609421 : Int) =
        (1 : Int) + (-718887227770819999014379347633017112416624980869909909429150134295330129261 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (26196891745479662166018536910674742527096560535262468254240532052418451808736 : Int) * ((36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (30251270830115116985930096146004015737257977999681908728532943911315493970531 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-1374816587603334730354449560707185487283075828204999698769542000387572444089 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) =
        (26196891745479662166018536910674742527096560535262468254240532052418451808736 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-13087931398729226766677399236245679756033304498516020401338991326543699063743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15500199270983955706652284227911074337502088724272782586135594828494004060240 : Int) =
        (26196891745479662166018536910674742527096560535262468254240532052418451808736 : Int) * ((36928369294575148816319232585394327370414037357207802071775198350103689751031 : Int) - (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int)) - (30251270830115116985930096146004015737257977999681908728532943911315493970531 : Int) + (-11981311329973719328365043839709991839571284457015133521786103919896980174413 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2039432827017687 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2039432827017687 : Nat) = 1019716413508843 + 1019716413508843 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep050
