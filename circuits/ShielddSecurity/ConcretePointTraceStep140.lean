import ShielddSecurity.ConcretePointTraceStep139
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep140
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30200237976945939805845381700852406729904423412891088117502848665621126106560
def inputY : F := 3645085658789680737882293952334866430386564382994536377295356382407268309750
def doubleX : F := 22808718604705256063912135982558957704035991869959184213195827094148312579036
def doubleY : F := 43720729742302932658189800306090436436144136875564719483920717754513938629189
def doubleSlope : F := 32063098086821842330437642552353891644942631762365288122807714423871486222034
def outX : F := 22808718604705256063912135982558957704035991869959184213195827094148312579036
def outY : F := 43720729742302932658189800306090436436144136875564719483920717754513938629189

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1262347776999085313464911089884377288582760 : Nat) • base) + ((1262347776999085313464911089884377288582760 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep139.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3645085658789680737882293952334866430386564382994536377295356382407268309750 : Int)) * (7228668192576331275116888901290507128909216415269441433939537927214353757214 : Int) =
        (1 : Int) + (1005003336853171777234223650792895047862799928993611506661754332801230848423 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (32063098086821842330437642552353891644942631762365288122807714423871486222034 : Int) * ((2 : Int) * (3645085658789680737882293952334866430386564382994536377295356382407268309750 : Int)) =
        (3 : Int) * (30200237976945939805845381700852406729904423412891088117502848665621126106560 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30200237976945939805845381700852406729904423412891088117502848665621126106560 : Int) + (-40964 : Int) * (-40964 : Int) + (-47723388523784638852752571218937413890056396246306373727914011090149374718072 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) =
        (32063098086821842330437642552353891644942631762365288122807714423871486222034 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30200237976945939805845381700852406729904423412891088117502848665621126106560 : Int) - (30200237976945939805845381700852406729904423412891088117502848665621126106560 : Int) + (-19605704214751564555840432789644996841881222153468623310448616264206245252336 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43720729742302932658189800306090436436144136875564719483920717754513938629189 : Int) =
        (32063098086821842330437642552353891644942631762365288122807714423871486222034 : Int) * ((30200237976945939805845381700852406729904423412891088117502848665621126106560 : Int) - (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int)) - (3645085658789680737882293952334866430386564382994536377295356382407268309750 : Int) + (-4519711168189279819804005405782980929622644380305879445461869029789133998029 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2524695553998170626929822179768754577165520 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2524695553998170626929822179768754577165520 : Nat) = 1262347776999085313464911089884377288582760 + 1262347776999085313464911089884377288582760 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep140
