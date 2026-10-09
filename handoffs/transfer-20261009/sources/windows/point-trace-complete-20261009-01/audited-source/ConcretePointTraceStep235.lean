import ShielddSecurity.ConcretePointTraceStep234
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep235
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18062882933548936926588002041462018784690172313961547866306186535222960580237
def inputY : F := 50525598120800224671539119945708881396506916521010517965741169178716074463038
def doubleX : F := 13447942686800389231367983183982820532645331781911569648135515858627341591149
def doubleY : F := 7704828932209652712621017002620400078167938076921390967124305740822422122842
def doubleSlope : F := 24993126331233835122989967083250173318613468531483790549842814745980405414596
def addX : F := 35191813858983665678840101937748681723872375468128827140518689859061474995749
def addY : F := 42448259498848719434447683340064418775674647435004070010040180303288892965194
def addSlope : F := 38160432587529809556126910452463064677247006630099214291249555703671653281811
def outX : F := 35191813858983665678840101937748681723872375468128827140518689859061474995749
def outY : F := 42448259498848719434447683340064418775674647435004070010040180303288892965194

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) • base) + ((50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep234.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (50525598120800224671539119945708881396506916521010517965741169178716074463038 : Int)) * (12018583819136078572063090850077074594173947566251618304321961026398066436429 : Int) =
        (1 : Int) + (23161476145815485949846466246300287422892403197091381579849022661921728857931 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24993126331233835122989967083250173318613468531483790549842814745980405414596 : Int) * ((2 : Int) * (50525598120800224671539119945708881396506916521010517965741169178716074463038 : Int)) =
        (3 : Int) * (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) + (-40964 : Int) * (-40964 : Int) + (29498546344642353213662237069246482978477388844132787010240268816197944236725 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int) =
        (24993126331233835122989967083250173318613468531483790549842814745980405414596 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) - (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) + (-11912767007755216423158005630636635617703895019203903353552846582017669412497 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (7704828932209652712621017002620400078167938076921390967124305740822422122842 : Int) =
        (24993126331233835122989967083250173318613468531483790549842814745980405414596 : Int) * ((18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) - (13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int)) - (50525598120800224671539119945708881396506916521010517965741169178716074463038 : Int) + (-2199673109543066224855492174596071677414093567146701228695131360060871157736 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) • base) + ((50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (36406216296177810064292255383104205555728655631158988941286721268651544050374 : Int) =
        (1 : Int) + (-18213058278241367496186841055521565774746876826616005180964440808459902071909 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (38160432587529809556126910452463064677247006630099214291249555703671653281811 : Int) * ((13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (7704828932209652712621017002620400078167938076921390967124305740822422122842 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-19090645866226683932301194070966493877354243780966374099122338178921911017090 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int) =
        (38160432587529809556126910452463064677247006630099214291249555703671653281811 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-27771418144617675825789751048699438235450528324920458470141961431306811386316 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42448259498848719434447683340064418775674647435004070010040180303288892965194 : Int) =
        (38160432587529809556126910452463064677247006630099214291249555703671653281811 : Int) * ((13447942686800389231367983183982820532645331781911569648135515858627341591149 : Int) - (35191813858983665678840101937748681723872375468128827140518689859061474995749 : Int)) - (7704828932209652712621017002620400078167938076921390967124305740822422122842 : Int) + (15824195310687609562218571734158127118836910925903405527775791444769855344972 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (100013494825603848418136101738330775904936542753178669454427477453494007 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (100013494825603848418136101738330775904936542753178669454427477453494007 : Nat) = 50006747412801924209068050869165387952468271376589334727213738726747003 + 50006747412801924209068050869165387952468271376589334727213738726747003 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep235
