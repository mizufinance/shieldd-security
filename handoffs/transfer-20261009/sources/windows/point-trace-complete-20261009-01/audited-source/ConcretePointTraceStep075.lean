import ShielddSecurity.ConcretePointTraceStep074
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep075
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 14090428345326626357970098522365631802949072654850059508085601349138350972482
def inputY : F := 15622441200651738356359453288114531138497638458394178828472229200618406159507
def doubleX : F := 11795585248532944556499366522838531862395664439098130792811295369797006297416
def doubleY : F := 39210695992692088523525366276007681561785770988638424123798056753943712564339
def doubleSlope : F := 38089125973686039488171695499463730708278296294653591610933341596937299141057
def addX : F := 18369007307486640951331358086771155548306762551965108385660059200984724505382
def addY : F := 12781459219896037092697101469326479412916386723360669015776463758550304921586
def addSlope : F := 8856506900364743934432459628183741202011420421606604516891226142207334058126
def outX : F := 18369007307486640951331358086771155548306762551965108385660059200984724505382
def outY : F := 12781459219896037092697101469326479412916386723360669015776463758550304921586

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((34216005056366384546611 : Nat) • base) + ((34216005056366384546611 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep074.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15622441200651738356359453288114531138497638458394178828472229200618406159507 : Int)) * (3188285442699566324199662073975709365317970774203807839211130334525492433395 : Int) =
        (1 : Int) + (1899798628062013797769114567712225964927531790410485911537793841588845737233 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (38089125973686039488171695499463730708278296294653591610933341596937299141057 : Int) * ((2 : Int) * (15622441200651738356359453288114531138497638458394178828472229200618406159507 : Int)) =
        (3 : Int) * (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) + (-40964 : Int) * (-40964 : Int) + (11337080709847641187256449783192218404641408078174557585516527769936839660714 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int) =
        (38089125973686039488171695499463730708278296294653591610933341596937299141057 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) - (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) + (-27667727726370175567062016925414951760778735886579526807603074635242256354749 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (39210695992692088523525366276007681561785770988638424123798056753943712564339 : Int) =
        (38089125973686039488171695499463730708278296294653591610933341596937299141057 : Int) * ((14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) - (11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int)) - (15622441200651738356359453288114531138497638458394178828472229200618406159507 : Int) + (-1666961169460598726071705634937184619811453540110939981870160109787454300532 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((34216005056366384546611 : Nat) • base) + ((34216005056366384546611 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (36978886998426138489657861856680299683875002470220977532903792781511872520516 : Int) =
        (1 : Int) + (-19664827520370253405523507673637948741902197771793938093656262835959992259821 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (8856506900364743934432459628183741202011420421606604516891226142207334058126 : Int) * ((11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (39210695992692088523525366276007681561785770988638424123798056753943712564339 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4709759940477769822919555167836470417718134288831615165631882215131823642595 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int) =
        (8856506900364743934432459628183741202011420421606604516891226142207334058126 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1495878808434888655983405684083412096657740847322312060873962679882927045451 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (12781459219896037092697101469326479412916386723360669015776463758550304921586 : Int) =
        (8856506900364743934432459628183741202011420421606604516891226142207334058126 : Int) * ((11795585248532944556499366522838531862395664439098130792811295369797006297416 : Int) - (18369007307486640951331358086771155548306762551965108385660059200984724505382 : Int)) - (39210695992692088523525366276007681561785770988638424123798056753943712564339 : Int) + (1110261965299468852358843418953694476609662662851170234520002203333754430857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (68432010112732769093223 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (68432010112732769093223 : Nat) = 34216005056366384546611 + 34216005056366384546611 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep075
