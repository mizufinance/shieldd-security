import ShielddSecurity.ConcretePointTraceStep164
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep165
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 17119618191088622730098396381817294085596503852139435327869958331837476286695
def inputY : F := 45402685746424772580864703624291120796294168146642407233914930396477023310166
def doubleX : F := 34069614590019166895498621531891361721357607003967070328640645138786448446345
def doubleY : F := 28205118793172743644184872752820207742980295864541469747726401145402064085420
def doubleSlope : F := 33490493777492833454324467726700449554129474801834576756674721141127746385913
def addX : F := 32149525223119013181030590267100696338684734941940479540715208589395925388380
def addY : F := 8242828718938693945061892169048049408741197662909424463389269845496230564948
def addSlope : F := 25511900829964994358670019780686279763188605641413826707935698873402161588946
def outX : F := 32149525223119013181030590267100696338684734941940479540715208589395925388380
def outY : F := 8242828718938693945061892169048049408741197662909424463389269845496230564948

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((42357362643666972212857043551571225592094601062297 : Nat) • base) + ((42357362643666972212857043551571225592094601062297 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep164.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (45402685746424772580864703624291120796294168146642407233914930396477023310166 : Int)) * (44112655379929757649240376522700299700407241949485834277202130930370619597545 : Int) =
        (1 : Int) + (76391707889539002643516846508407271151695180887947839622862618893430832817803 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (33490493777492833454324467726700449554129474801834576756674721141127746385913 : Int) * ((2 : Int) * (45402685746424772580864703624291120796294168146642407233914930396477023310166 : Int)) =
        (3 : Int) * (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) + (-40964 : Int) * (-40964 : Int) + (41228886534228474673768442102191040615804439203691329002065434805454610786905 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int) =
        (33490493777492833454324467726700449554129474801834576756674721141127746385913 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) - (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) + (-21390186961012937060251094685014994261880583729101544262038983846246866467554 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (28205118793172743644184872752820207742980295864541469747726401145402064085420 : Int) =
        (33490493777492833454324467726700449554129474801834576756674721141127746385913 : Int) * ((17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) - (34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int)) - (45402685746424772580864703624291120796294168146642407233914930396477023310166 : Int) + (10825865822416745863040026033593702698161797766423010915715785801795362074772 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((42357362643666972212857043551571225592094601062297 : Nat) • base) + ((42357362643666972212857043551571225592094601062297 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (28401803721580482162590750238254143131887507480754952126717345632403195887827 : Int) =
        (1 : Int) + (-3038970364658571657724311031605762715389746001795235726655478885650993535679 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (25511900829964994358670019780686279763188605641413826707935698873402161588946 : Int) * ((34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (28205118793172743644184872752820207742980295864541469747726401145402064085420 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2729753058234912335979477747823251431577899383305968916257258315257262637494 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) =
        (25511900829964994358670019780686279763188605641413826707935698873402161588946 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-12412438655485876257518720546058531063081736778769698285848548958075373325652 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (8242828718938693945061892169048049408741197662909424463389269845496230564948 : Int) =
        (25511900829964994358670019780686279763188605641413826707935698873402161588946 : Int) * ((34069614590019166895498621531891361721357607003967070328640645138786448446345 : Int) - (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int)) - (28205118793172743644184872752820207742980295864541469747726401145402064085420 : Int) + (-934191130584273805608338985553439705121461646443810686208229740958146793194 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (84714725287333944425714087103142451184189202124595 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (84714725287333944425714087103142451184189202124595 : Nat) = 42357362643666972212857043551571225592094601062297 + 42357362643666972212857043551571225592094601062297 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep165
