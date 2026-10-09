import ShielddSecurity.ConcretePointTraceStep235
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep236
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 35191813858983665678840101937748681723872375468128827140518689859061474995749
def inputY : F := 42448259498848719434447683340064418775674647435004070010040180303288892965194
def doubleX : F := 27773554920041364505085995361419327845912299105049653420724124587957958911846
def doubleY : F := 3414698383588415840330958276745785235120339748107241774314788446047725028193
def doubleSlope : F := 2784727859585239887819538236227870587488097764625795302616047137968039268927
def outX : F := 27773554920041364505085995361419327845912299105049653420724124587957958911846
def outY : F := 3414698383588415840330958276745785235120339748107241774314788446047725028193

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((100013494825603848418136101738330775904936542753178669454427477453494007 : Nat) • base) + ((100013494825603848418136101738330775904936542753178669454427477453494007 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep235.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42448259498848719434447683340064418775674647435004070010040180303288892965194 : Int)) * (6815206382272193511218812859514634344377438459375077767648974133366780504733 : Int) =
        (1 : Int) + (11034187875637143894056220158620844129424100741036528417367212316444958350531 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (2784727859585239887819538236227870587488097764625795302616047137968039268927 : Int) * ((2 : Int) * (42448259498848719434447683340064418775674647435004070010040180303288892965194 : Int)) =
        (3 : Int) * (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) + (-40964 : Int) * (-40964 : Int) + (-66347277981004850661582337440134644049658807627635205253273806252783469922143 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) =
        (2784727859585239887819538236227870587488097764625795302616047137968039268927 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) - (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) + (-147889383481269020103734340222805499401748056757402491155094762815675934681 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3414698383588415840330958276745785235120339748107241774314788446047725028193 : Int) =
        (2784727859585239887819538236227870587488097764625795302616047137968039268927 : Int) * ((35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) - (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int)) - (42448259498848719434447683340064418775674647435004070010040180303288892965194 : Int) + (-393963717929690350227167296536310258613622965508917825827433500130439844438 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (200026989651207696836272203476661551809873085506357338908854954906988014 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (200026989651207696836272203476661551809873085506357338908854954906988014 : Nat) = 100013494825603848418136101738330775904936542753178669454427477453494007 + 100013494825603848418136101738330775904936542753178669454427477453494007 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep236
