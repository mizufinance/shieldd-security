import ShielddSecurity.ConcretePointTraceStep011
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep012
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10333346777456882902386196603700873278109877246905663873291420660941068575558
def inputY : F := 38282350565661677357258825406497303688287425657349814821184155678355197368099
def doubleX : F := 45263819376656558113406654378903099433695296629883620542501702553041750026032
def doubleY : F := 51326265900794861778597942363284813730718707987719594191926188907758864251846
def doubleSlope : F := 33633255120158516804121196182550929507972559544449760673888947879294665536293
def addX : F := 9615612681959853836191120892692185353859817150479829011104681583320823510738
def addY : F := 42327772510509623778676028940091341497326703384054299441788045192093919904545
def addSlope : F := 51033454710397648929944585334624060103296044704590735330391710494908694515638
def outX : F := 9615612681959853836191120892692185353859817150479829011104681583320823510738
def outY : F := 42327772510509623778676028940091341497326703384054299441788045192093919904545

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3709 : Nat) • base) + ((3709 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep011.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (38282350565661677357258825406497303688287425657349814821184155678355197368099 : Int)) * (10666370667799191407753550565939982768369307675024692752064169326399644980528 : Int) =
        (1 : Int) + (15574594294620612888036862791856425950461875116067784229909441210741246913311 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (33633255120158516804121196182550929507972559544449760673888947879294665536293 : Int) * ((2 : Int) * (38282350565661677357258825406497303688287425657349814821184155678355197368099 : Int)) =
        (3 : Int) * (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) + (-40964 : Int) * (-40964 : Int) + (43000826284454703376376236877817817781753780794681709466530728168018114130178 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int) =
        (33633255120158516804121196182550929507972559544449760673888947879294665536293 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) - (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) + (-21572937348707974288531098547715540676095341024654510028994810486188190651813 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (51326265900794861778597942363284813730718707987719594191926188907758864251846 : Int) =
        (33633255120158516804121196182550929507972559544449760673888947879294665536293 : Int) * ((10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) - (45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int)) - (38282350565661677357258825406497303688287425657349814821184155678355197368099 : Int) + (22404994528514836675931989863345162957783702258019826948020927011665378165179 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3709 : Nat) • base) + ((3709 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (21317209367009398465530007383554181218008066638768124176171363933945211552221 : Int) =
        (1 : Int) + (2269952372403540569238250755362942900253283872467612121111664417636378818056 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (51033454710397648929944585334624060103296044704590735330391710494908694515638 : Int) * ((45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (51326265900794861778597942363284813730718707987719594191926188907758864251846 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (5434271887909290983451460993879139683629501861922953532015136422991515260674 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int) =
        (51033454710397648929944585334624060103296044704590735330391710494908694515638 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-49668542595693222053867454918651265443040110414746854295945581344821813907543 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42327772510509623778676028940091341497326703384054299441788045192093919904545 : Int) =
        (51033454710397648929944585334624060103296044704590735330391710494908694515638 : Int) * ((45263819376656558113406654378903099433695296629883620542501702553041750026032 : Int) - (9615612681959853836191120892692185353859817150479829011104681583320823510738 : Int)) - (51326265900794861778597942363284813730718707987719594191926188907758864251846 : Int) + (-34694779781680651147235242186229114136710126488491634558772907460739865683437 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (7419 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (7419 : Nat) = 3709 + 3709 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep012
