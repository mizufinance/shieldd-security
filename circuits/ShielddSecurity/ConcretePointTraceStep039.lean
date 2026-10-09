import ShielddSecurity.ConcretePointTraceStep038
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep039
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15764005122552086306320359007029587902914078351527556558239811269606240069132
def inputY : F := 34699216161072689576544176653058496837137716526195330229824724896790667213095
def doubleX : F := 18192038621732592077226555563000659613273658317843497912292200102131098444546
def doubleY : F := 46217943257432562574704279169318004911947942208083293832149232440075395492669
def doubleSlope : F := 17813178747008247048683886055879944959066274459563754186303112193133067565281
def addX : F := 37095792594886011083730407017681406074810939576811039535522710964352359401094
def addY : F := 15568696161607701885604510534197001426578067509354509498043331346571390510964
def addSlope : F := 24642323361392473218171818714177555159154074815130754239877891850573865752193
def outX : F := 37095792594886011083730407017681406074810939576811039535522710964352359401094
def outY : F := 15568696161607701885604510534197001426578067509354509498043331346571390510964

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((497908405033 : Nat) • base) + ((497908405033 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep038.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (34699216161072689576544176653058496837137716526195330229824724896790667213095 : Int)) * (12199570882018273320879679470369679543512975268430990189546515328735801415125 : Int) =
        (1 : Int) + (16146027722191500089324024945532548021821325722423644658291811086640242131173 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (17813178747008247048683886055879944959066274459563754186303112193133067565281 : Int) * ((2 : Int) * (34699216161072689576544176653058496837137716526195330229824724896790667213095 : Int)) =
        (3 : Int) * (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) + (-40964 : Int) * (-40964 : Int) + (9358003572290030226426937323495297137496700348317247299530784299967173145998 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int) =
        (17813178747008247048683886055879944959066274459563754186303112193133067565281 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) - (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) + (-6051378679446302880112145492713636900110197399574063581925569307225172428463 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (46217943257432562574704279169318004911947942208083293832149232440075395492669 : Int) =
        (17813178747008247048683886055879944959066274459563754186303112193133067565281 : Int) * ((15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) - (18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int)) - (34699216161072689576544176653058496837137716526195330229824724896790667213095 : Int) + (824835946385482732279977520486708294392072620086248840739959202177467451546 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((497908405033 : Nat) • base) + ((497908405033 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (35182732457408889951373834870099208858577243640919416255384907226824041324992 : Int) =
        (1 : Int) + (-14417851003658718234873830400996601254172931941638768801439472964687835790785 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (24642323361392473218171818714177555159154074815130754239877891850573865752193 : Int) * ((18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (46217943257432562574704279169318004911947942208083293832149232440075395492669 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-10098401169910190027335026229962221285653358751396567892414793619387267326628 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (37095792594886011083730407017681406074810939576811039535522710964352359401094 : Int) =
        (24642323361392473218171818714177555159154074815130754239877891850573865752193 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-11580699256364950453696661623130700691565778507549133359272746285709958601838 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15568696161607701885604510534197001426578067509354509498043331346571390510964 : Int) =
        (24642323361392473218171818714177555159154074815130754239877891850573865752193 : Int) * ((18192038621732592077226555563000659613273658317843497912292200102131098444546 : Int) - (37095792594886011083730407017681406074810939576811039535522710964352359401094 : Int)) - (46217943257432562574704279169318004911947942208083293832149232440075395492669 : Int) + (8883849398810634497307895101078646634513882435939685300467253395448854614069 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (995816810067 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (995816810067 : Nat) = 497908405033 + 497908405033 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep039
