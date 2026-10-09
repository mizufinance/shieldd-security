import ShielddSecurity.ConcretePointTraceStep216
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep217
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31807404585560487380869877515858187052475130286902328101832048210678012912779
def inputY : F := 48411753480801839013272274296788929974729909911120472290649729964566788389298
def doubleX : F := 11008989912967702846955004471917208641962447016336137389692909982508546763941
def doubleY : F := 13569424269860700681373744138409655908617544646135229869481047480064772580439
def doubleSlope : F := 52306405598999721564212018231035517925051908811705856548599766623180640022410
def addX : F := 10724188342417030891003097423720145462555944081428678643909075073409293381345
def addY : F := 6127007311068192843481224551910551901395497836339022159079395079838224180845
def addSlope : F := 8118769509773755347908208355314271852059432529166024347647765019564824229487
def outX : F := 10724188342417030891003097423720145462555944081428678643909075073409293381345
def outY : F := 6127007311068192843481224551910551901395497836339022159079395079838224180845

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((190760602618415543400070384480153610048173032289845789822440104395 : Nat) • base) + ((190760602618415543400070384480153610048173032289845789822440104395 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep216.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (48411753480801839013272274296788929974729909911120472290649729964566788389298 : Int)) * (7841283379867469244424825298262055607377892310624955956454242454214185169092 : Int) =
        (1 : Int) + (14479028973633946990057744384484705591275486183708311361872404170108883769487 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (52306405598999721564212018231035517925051908811705856548599766623180640022410 : Int) * ((2 : Int) * (48411753480801839013272274296788929974729909911120472290649729964566788389298 : Int)) =
        (3 : Int) * (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) + (-40964 : Int) * (-40964 : Int) + (38701683922790145347524500377517761444643334494551100402735551780504301743645 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int) =
        (52306405598999721564212018231035517925051908811705856548599766623180640022410 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) - (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) + (-52177255696590652888590048650544041902212488134376246325003271696041557672113 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (13569424269860700681373744138409655908617544646135229869481047480064772580439 : Int) =
        (52306405598999721564212018231035517925051908811705856548599766623180640022410 : Int) * ((31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) - (11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int)) - (48411753480801839013272274296788929974729909911120472290649729964566788389298 : Int) + (-20747061244757933119844790427932509691033472490290435461258963751111136935411 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((190760602618415543400070384480153610048173032289845789822440104395 : Nat) • base) + ((190760602618415543400070384480153610048173032289845789822440104395 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34604470423604815659010410518276062869178993517165686728710433144277231553798 : Int) =
        (1 : Int) + (-18921252563835653074527817562943287177201633623294320257666327455808862581909 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (8118769509773755347908208355314271852059432529166024347647765019564824229487 : Int) * ((11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (13569424269860700681373744138409655908617544646135229869481047480064772580439 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4439232461052492591197959365999142968856220613978250168739195343623045341919 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (10724188342417030891003097423720145462555944081428678643909075073409293381345 : Int) =
        (8118769509773755347908208355314271852059432529166024347647765019564824229487 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1257048120827390314051114825620379466956506764232410246693260509926533185936 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (6127007311068192843481224551910551901395497836339022159079395079838224180845 : Int) =
        (8118769509773755347908208355314271852059432529166024347647765019564824229487 : Int) * ((11008989912967702846955004471917208641962447016336137389692909982508546763941 : Int) - (10724188342417030891003097423720145462555944081428678643909075073409293381345 : Int)) - (13569424269860700681373744138409655908617544646135229869481047480064772580439 : Int) + (-44096494996984857627187280560672026380408195711289461812423746037849396536 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (381521205236831086800140768960307220096346064579691579644880208791 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (381521205236831086800140768960307220096346064579691579644880208791 : Nat) = 190760602618415543400070384480153610048173032289845789822440104395 + 190760602618415543400070384480153610048173032289845789822440104395 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep217
