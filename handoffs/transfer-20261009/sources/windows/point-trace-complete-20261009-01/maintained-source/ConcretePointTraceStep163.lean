import ShielddSecurity.ConcretePointTraceStep162
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep163
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 50797614216433334324982388977054778939506887512575850481165984850270269274776
def inputY : F := 24209236923270452333653518572264115681877987503218851686518981732370096861068
def doubleX : F := 11707724010248953370437236779096914052462899176762174687169726617337109660280
def doubleY : F := 16398859468295218015857475547959228430893047628913126055031874553951297577848
def doubleSlope : F := 45452531700529284088296779716137269248891659621213917705532688979035737131772
def outX : F := 11707724010248953370437236779096914052462899176762174687169726617337109660280
def outY : F := 16398859468295218015857475547959228430893047628913126055031874553951297577848

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((10589340660916743053214260887892806398023650265574 : Nat) • base) + ((10589340660916743053214260887892806398023650265574 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep162.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24209236923270452333653518572264115681877987503218851686518981732370096861068 : Int)) * (16044434742103552154401147494332470290292706496225786768348803289079630067978 : Int) =
        (1 : Int) + (14815182188693269382518303217842963047943669095417167655496958159209464205039 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (45452531700529284088296779716137269248891659621213917705532688979035737131772 : Int) * ((2 : Int) * (24209236923270452333653518572264115681877987503218851686518981732370096861068 : Int)) =
        (3 : Int) * (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) + (-40964 : Int) * (-40964 : Int) + (-105661450187291319136226919200788968318760785263494402124508382333907831388592 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) =
        (45452531700529284088296779716137269248891659621213917705532688979035737131772 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) - (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) + (-39399221069311497135832941925717252766084043823706198724684510638506298749040 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (16398859468295218015857475547959228430893047628913126055031874553951297577848 : Int) =
        (45452531700529284088296779716137269248891659621213917705532688979035737131772 : Int) * ((50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) - (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int)) - (24209236923270452333653518572264115681877987503218851686518981732370096861068 : Int) + (-33883948114393781291981718005294301238338908956025241060531035731147104365692 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (21178681321833486106428521775785612796047300531148 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (21178681321833486106428521775785612796047300531148 : Nat) = 10589340660916743053214260887892806398023650265574 + 10589340660916743053214260887892806398023650265574 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep163
