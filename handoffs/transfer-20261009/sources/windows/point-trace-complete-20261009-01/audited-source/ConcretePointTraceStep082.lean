import ShielddSecurity.ConcretePointTraceStep081
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep082
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3592619559029744071302652922465033624567307736147135569179248253630476051480
def inputY : F := 2390729998028047014141432011711265607351043552138256735345189118532694064024
def doubleX : F := 18962406183220949977999057953829821799192576723294720021709754897375347352968
def doubleY : F := 43733616238204847427995007778728273343205133230803238768422842786782594220548
def doubleSlope : F := 42279502039981715548150917902729140499202686024059479572423156020753551580337
def addX : F := 30528867951713540512048687902432589990364788194140891424918383835404655526180
def addY : F := 1312794557321096679255480179769140058270383445927890526788999230382539141520
def addSlope : F := 44360063793115290877863942515093291676308875105325356888361987582514568945255
def outX : F := 30528867951713540512048687902432589990364788194140891424918383835404655526180
def outY : F := 1312794557321096679255480179769140058270383445927890526788999230382539141520

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4379648647214897221966286 : Nat) • base) + ((4379648647214897221966286 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep081.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2390729998028047014141432011711265607351043552138256735345189118532694064024 : Int)) * (9792212275140629917054202833950851700383366613917171363430259760425067510650 : Int) =
        (1 : Int) + (892920564596291660555732539681658980224066746280815944815621757590174489823 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (42279502039981715548150917902729140499202686024059479572423156020753551580337 : Int) * ((2 : Int) * (2390729998028047014141432011711265607351043552138256735345189118532694064024 : Int)) =
        (3 : Int) * (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) + (-40964 : Int) * (-40964 : Int) + (3116892799514183995202730953967342135780573928267599514619823358501210333920 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int) =
        (42279502039981715548150917902729140499202686024059479572423156020753551580337 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) - (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) + (-34090330079906331447326284237213981252224145966804104837390893491133384918193 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43733616238204847427995007778728273343205133230803238768422842786782594220548 : Int) =
        (42279502039981715548150917902729140499202686024059479572423156020753551580337 : Int) * ((3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) - (18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int)) - (2390729998028047014141432011711265607351043552138256735345189118532694064024 : Int) + (12392792582583454952720304386852835057319786529990893933694393798391436934156 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((4379648647214897221966286 : Nat) • base) + ((4379648647214897221966286 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34793567903917010774653707155705819537639411964018338711592105491812388886837 : Int) =
        (1 : Int) + (-13747198113300740172673186549976312592382646702359866092309967155402457408712 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (44360063793115290877863942515093291676308875105325356888361987582514568945255 : Int) * ((18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (43733616238204847427995007778728273343205133230803238768422842786782594220548 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-17526991970661381524951418503478833605412413654546417177772929632472423489479 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) =
        (44360063793115290877863942515093291676308875105325356888361987582514568945255 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-37528033110100988940950004672555685137116868849953991939692257345965676396474 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (1312794557321096679255480179769140058270383445927890526788999230382539141520 : Int) =
        (44360063793115290877863942515093291676308875105325356888361987582514568945255 : Int) * ((18962406183220949977999057953829821799192576723294720021709754897375347352968 : Int) - (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int)) - (43733616238204847427995007778728273343205133230803238768422842786782594220548 : Int) + (9785075202756461625856151801950056838938110281426718226034903272684899456856 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (8759297294429794443932573 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (8759297294429794443932573 : Nat) = 4379648647214897221966286 + 4379648647214897221966286 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep082
