import ShielddSecurity.ConcretePointTraceStep161
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep162
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15404267638426985390272097218400946617754616138581192216781492137569353797187
def inputY : F := 4072985716889950744564801902672042965456180286556136476577763122841076849901
def doubleX : F := 50797614216433334324982388977054778939506887512575850481165984850270269274776
def doubleY : F := 24209236923270452333653518572264115681877987503218851686518981732370096861068
def doubleSlope : F := 17585244525248709592847460309592716018478013590388531642063178963806812485679
def outX : F := 50797614216433334324982388977054778939506887512575850481165984850270269274776
def outY : F := 24209236923270452333653518572264115681877987503218851686518981732370096861068

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5294670330458371526607130443946403199011825132787 : Nat) • base) + ((5294670330458371526607130443946403199011825132787 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep161.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (4072985716889950744564801902672042965456180286556136476577763122841076849901 : Int)) * (36645267019443543060193718213693581090900183099246264306713825532950793992585 : Int) =
        (1 : Int) + (5692882922744227240166368729434604359392343164819951416622221845297928601513 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (17585244525248709592847460309592716018478013590388531642063178963806812485679 : Int) * ((2 : Int) * (4072985716889950744564801902672042965456180286556136476577763122841076849901 : Int)) =
        (3 : Int) * (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) + (-40964 : Int) * (-40964 : Int) + (-10844207004670974310129885657637237741379127288703458046805793482926745648501 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int) =
        (17585244525248709592847460309592716018478013590388531642063178963806812485679 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) - (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) + (-5897504789993151948568365542829985790685406188755344130644702270074491650443 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24209236923270452333653518572264115681877987503218851686518981732370096861068 : Int) =
        (17585244525248709592847460309592716018478013590388531642063178963806812485679 : Int) * ((15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) - (50797614216433334324982388977054778939506887512575850481165984850270269274776 : Int)) - (4072985716889950744564801902672042965456180286556136476577763122841076849901 : Int) + (11869748565508107752754279342016093255496826488460712971496098875185237985300 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (10589340660916743053214260887892806398023650265574 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (10589340660916743053214260887892806398023650265574 : Nat) = 5294670330458371526607130443946403199011825132787 + 5294670330458371526607130443946403199011825132787 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep162
