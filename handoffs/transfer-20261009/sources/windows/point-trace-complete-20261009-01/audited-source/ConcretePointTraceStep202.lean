import ShielddSecurity.ConcretePointTraceStep201
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep202
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12189058057469396823932366284755724066207170687485414246282943715765456356768
def inputY : F := 27827872333113970240299072461453037450701473764736709678527325927296938478706
def doubleX : F := 19349527984996487913048392273538059565902980988508868888824997387533467296767
def doubleY : F := 19534138463519650757599083740957050634918546857075710620634812219873893689947
def doubleSlope : F := 27003294324288439897733024207059831229722698423150757958697316414340220556409
def addX : F := 10130666718819175285113361282515029354779409130751530781402943239498125319793
def addY : F := 13733683658468600921724714767127161246474265720849013178763607005477553543462
def addSlope : F := 50142649819379498051988246944130685459349008108973549746502300924790676697379
def outX : F := 10130666718819175285113361282515029354779409130751530781402943239498125319793
def outY : F := 13733683658468600921724714767127161246474265720849013178763607005477553543462

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5821551593579575909425976088871875306645905526423516535108645 : Nat) • base) + ((5821551593579575909425976088871875306645905526423516535108645 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep201.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (27827872333113970240299072461453037450701473764736709678527325927296938478706 : Int)) * (3979766951527872849454601813727665627246414123191409228762769882298754067112 : Int) =
        (1 : Int) + (4224147924404211922855930628416916665594603913627594168310963790345528196511 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (27003294324288439897733024207059831229722698423150757958697316414340220556409 : Int) * ((2 : Int) * (27827872333113970240299072461453037450701473764736709678527325927296938478706 : Int)) =
        (3 : Int) * (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) + (-40964 : Int) * (-40964 : Int) + (20161178611852482189350766359931250872979033348140928422658097812766162289076 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int) =
        (27003294324288439897733024207059831229722698423150757958697316414340220556409 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) - (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) + (-13906088187311225819490147555264995273610171904011747929470180758749530075642 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (19534138463519650757599083740957050634918546857075710620634812219873893689947 : Int) =
        (27003294324288439897733024207059831229722698423150757958697316414340220556409 : Int) * ((12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) - (19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int)) - (27827872333113970240299072461453037450701473764736709678527325927296938478706 : Int) + (3687480685836860935369599000806319195194759544803958776163172505529166052788 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((5821551593579575909425976088871875306645905526423516535108645 : Nat) • base) + ((5821551593579575909425976088871875306645905526423516535108645 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (1907416716647889402992811339662097824780547284956791589049566897588070991914 : Int) =
        (1 : Int) + (-739552555715129276886962663697218863935748655820516471567928504368272286025 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (50142649819379498051988246944130685459349008108973549746502300924790676697379 : Int) * ((19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (19534138463519650757599083740957050634918546857075710620634812219873893689947 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-19441543371508810493862101882162693593779091981073704942512215037449184993005 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) =
        (50142649819379498051988246944130685459349008108973549746502300924790676697379 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-47949716153524045971947990816399617800640846243103095665849930668320757711182 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (13733683658468600921724714767127161246474265720849013178763607005477553543462 : Int) =
        (50142649819379498051988246944130685459349008108973549746502300924790676697379 : Int) * ((19349527984996487913048392273538059565902980988508868888824997387533467296767 : Int) - (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int)) - (19534138463519650757599083740957050634918546857075710620634812219873893689947 : Int) + (-8815684503396066761709265665026254991627344276218949932518285499389206998249 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (11643103187159151818851952177743750613291811052847033070217291 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (11643103187159151818851952177743750613291811052847033070217291 : Nat) = 5821551593579575909425976088871875306645905526423516535108645 + 5821551593579575909425976088871875306645905526423516535108645 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep202
