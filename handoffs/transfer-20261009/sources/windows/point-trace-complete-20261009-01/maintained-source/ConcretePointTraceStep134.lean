import ShielddSecurity.ConcretePointTraceStep133
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep134
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44319826743251418605552096911184252296135959549460594984336300895864160026666
def inputY : F := 4066007365998513237822314428336016727463879784035898691569132468071648916250
def doubleX : F := 5824370324129131819914424543520891705675313770785620746584122423326382521430
def doubleY : F := 19112838113654319849700338239750646468434685250940017862930899750049568664062
def doubleSlope : F := 34418971095357188487335011113879706054842327581404391246350784931939671805600
def addX : F := 33530012567401633416188405601731313059370972882221910562353588373737862126615
def addY : F := 11554434862399335102618729118232673020426251621533399057355725112970755872642
def addSlope : F := 959680464122551483455164330778553448599869733384122525697213874771065667
def outX : F := 33530012567401633416188405601731313059370972882221910562353588373737862126615
def outY : F := 11554434862399335102618729118232673020426251621533399057355725112970755872642

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((19724184015610708022889235779443395134105 : Nat) • base) + ((19724184015610708022889235779443395134105 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep133.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (4066007365998513237822314428336016727463879784035898691569132468071648916250 : Int)) * (17019889049969367138908287672497091898504921356303336845127545306877753813299 : Int) =
        (1 : Int) + (2639528529447733877687797898331712187448156397504645132789583519146485624923 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (34418971095357188487335011113879706054842327581404391246350784931939671805600 : Int) * ((2 : Int) * (4066007365998513237822314428336016727463879784035898691569132468071648916250 : Int)) =
        (3 : Int) * (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) + (-40964 : Int) * (-40964 : Int) + (-107042087671884438192343583309165657709053981991598367859698642519667028875676 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int) =
        (34418971095357188487335011113879706054842327581404391246350784931939671805600 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) - (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) + (-22592653737664685438523834699648458587757010237548744943292605865147403085662 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (19112838113654319849700338239750646468434685250940017862930899750049568664062 : Int) =
        (34418971095357188487335011113879706054842327581404391246350784931939671805600 : Int) * ((44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) - (5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int)) - (4066007365998513237822314428336016727463879784035898691569132468071648916250 : Int) + (-25268463573215523973746068143566027313767939922672149979818954528152498659176 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((19724184015610708022889235779443395134105 : Nat) • base) + ((19724184015610708022889235779443395134105 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (41121575848777119194859410447771336697822600605786322099569204924546318209764 : Int) =
        (1 : Int) + (-26550630346532335830128994341336228282795139506399146656250755373182761458261 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (959680464122551483455164330778553448599869733384122525697213874771065667 : Int) * ((5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (19112838113654319849700338239750646468434685250940017862930899750049568664062 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-619629008076162635590822151241243307103734590532049770997371337628720459 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (33530012567401633416188405601731313059370972882221910562353588373737862126615 : Int) =
        (959680464122551483455164330778553448599869733384122525697213874771065667 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-17564054955553803408248576550219086036687195497097228563859633468433 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (11554434862399335102618729118232673020426251621533399057355725112970755872642 : Int) =
        (959680464122551483455164330778553448599869733384122525697213874771065667 : Int) * ((5824370324129131819914424543520891705675313770785620746584122423326382521430 : Int) - (33530012567401633416188405601731313059370972882221910562353588373737862126615 : Int)) - (19112838113654319849700338239750646468434685250940017862930899750049568664062 : Int) + (507068176473382101627947114474558780032538256646252410633617141041925123 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (39448368031221416045778471558886790268211 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (39448368031221416045778471558886790268211 : Nat) = 19724184015610708022889235779443395134105 + 19724184015610708022889235779443395134105 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep134
