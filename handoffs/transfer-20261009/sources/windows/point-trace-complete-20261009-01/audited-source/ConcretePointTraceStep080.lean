import ShielddSecurity.ConcretePointTraceStep079
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep080
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39727463118715422421356341345265883120716365406746825838388955238009483265663
def inputY : F := 18278318055383336226248808441008042950102267839158647487505823703875746485647
def doubleX : F := 22930048271573388628211301785012055521003630918544390388438597333388728014243
def doubleY : F := 17580816986642622115127286413696250295612815424194397050902885814497428020575
def doubleSlope : F := 13376646892512169846110135257837159412306154034049067713702574626434518366835
def addX : F := 12426011185503422633767884078312640800199031477463737358107803603538291618288
def addY : F := 49445160941242159412468737629693755242696987535313224428994431235309232460016
def addSlope : F := 37013444921749783172190396764327722504829488314483187946011111243938793882867
def outX : F := 12426011185503422633767884078312640800199031477463737358107803603538291618288
def outY : F := 49445160941242159412468737629693755242696987535313224428994431235309232460016

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1094912161803724305491571 : Nat) • base) + ((1094912161803724305491571 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep079.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18278318055383336226248808441008042950102267839158647487505823703875746485647 : Int)) * (29491275603550650335407301867275091769788965791327419136735677340648184246409 : Int) =
        (1 : Int) + (20560385939600890277316567693737149725471981926640962889349462213363407172365 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13376646892512169846110135257837159412306154034049067713702574626434518366835 : Int) * ((2 : Int) * (18278318055383336226248808441008042950102267839158647487505823703875746485647 : Int)) =
        (3 : Int) * (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) + (-40964 : Int) * (-40964 : Int) + (-80971448469862968078683383176491753001887695170259032823973634910632962295465 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int) =
        (13376646892512169846110135257837159412306154034049067713702574626434518366835 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) - (39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) + (-3412447708545848097635400858703687902251797161703954316402126853231669144848 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (17580816986642622115127286413696250295612815424194397050902885814497428020575 : Int) =
        (13376646892512169846110135257837159412306154034049067713702574626434518366835 : Int) * ((39727463118715422421356341345265883120716365406746825838388955238009483265663 : Int) - (22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int)) - (18278318055383336226248808441008042950102267839158647487505823703875746485647 : Int) + (-4285102258078589067632775870900419989447045802500126973377188714488838264806 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1094912161803724305491571 : Nat) • base) + ((1094912161803724305491571 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (45877797816075434071678611749918052883326472776505955801700057876516865139733 : Int) =
        (1 : Int) + (-14655245039716271609114764189594801920765234893372056697108248202602005524017 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (37013444921749783172190396764327722504829488314483187946011111243938793882867 : Int) * ((22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (17580816986642622115127286413696250295612815424194397050902885814497428020575 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-11823608170273057421164323915527155956394684678260348948054796426237341065093 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) =
        (37013444921749783172190396764327722504829488314483187946011111243938793882867 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-26127057103555015217160049853795660545584488067540786409967518668072156057611 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (49445160941242159412468737629693755242696987535313224428994431235309232460016 : Int) =
        (37013444921749783172190396764327722504829488314483187946011111243938793882867 : Int) * ((22930048271573388628211301785012055521003630918544390388438597333388728014243 : Int) - (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int)) - (17580816986642622115127286413696250295612815424194397050902885814497428020575 : Int) + (-7414591571949139725014613646615340399726059542112250149581254845809517789338 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2189824323607448610983143 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2189824323607448610983143 : Nat) = 1094912161803724305491571 + 1094912161803724305491571 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep080
