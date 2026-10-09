import ShielddSecurity.ConcretePointTraceStep005
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep006
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41283911756810255122586575491328845087064416522079797081782609301767538420142
def inputY : F := 2915854498086107523456245359524550650266537620604363330686602258345388509879
def doubleX : F := 23630897774259757591614879164927094358974626924066810539045135729981301280172
def doubleY : F := 27543387322889419804187057959145703072357160490673448501297199581896659969209
def doubleSlope : F := 4088249876732352713798804497244406023495059662870926800204891596251835515518
def addX : F := 21933938387720517397777775700475712951098354028738066484391338187786808861578
def addY : F := 16390246766700321050481125259312507925865235543189173088893915032765084532165
def addSlope : F := 23806219807970881755910937424704278190378263657252491027650681263446459858943
def outX : F := 21933938387720517397777775700475712951098354028738066484391338187786808861578
def outY : F := 16390246766700321050481125259312507925865235543189173088893915032765084532165

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((57 : Nat) • base) + ((57 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep005.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2915854498086107523456245359524550650266537620604363330686602258345388509879 : Int)) * (11888087301235378601424586886528611464979635147494715678072932356464360582339 : Int) =
        (1 : Int) + (1322145676606954517544102548901665522337861125625346708359389557422539127497 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (4088249876732352713798804497244406023495059662870926800204891596251835515518 : Int) * ((2 : Int) * (2915854498086107523456245359524550650266537620604363330686602258345388509879 : Int)) =
        (3 : Int) * (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) + (-40964 : Int) * (-40964 : Int) + (-97056502046555197968388711156727776611847246399558195007930249541402766152664 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int) =
        (4088249876732352713798804497244406023495059662870926800204891596251835515518 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) - (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) + (-318747174501829496746180588079768325228669120706618673291788656056356263172 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27543387322889419804187057959145703072357160490673448501297199581896659969209 : Int) =
        (4088249876732352713798804497244406023495059662870926800204891596251835515518 : Int) * ((41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) - (23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int)) - (2915854498086107523456245359524550650266537620604363330686602258345388509879 : Int) + (-1376346480288204488223241779743313101847376084102083741768417305963317173644 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((57 : Nat) • base) + ((57 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (16530338437751303215558235680025655894392446197457918825506406648135826584816 : Int) =
        (1 : Int) + (-5059524339459559161142366038702851156972902813293272455511614744351053200529 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (23806219807970881755910937424704278190378263657252491027650681263446459858943 : Int) * ((23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (27543387322889419804187057959145703072357160490673448501297199581896659969209 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-7286490170937967551346701346236799294889821567206094355605411448690684690472 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) =
        (23806219807970881755910937424704278190378263657252491027650681263446459858943 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-10808174740149386235035257954928441050520038292296390965009887527053394962368 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (16390246766700321050481125259312507925865235543189173088893915032765084532165 : Int) =
        (23806219807970881755910937424704278190378263657252491027650681263446459858943 : Int) * ((23630897774259757591614879164927094358974626924066810539045135729981301280172 : Int) - (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int)) - (27543387322889419804187057959145703072357160490673448501297199581896659969209 : Int) + (-770430321344500283198269270762459856439736501806823800542497397943636407136 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (115 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (115 : Nat) = 57 + 57 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep006
