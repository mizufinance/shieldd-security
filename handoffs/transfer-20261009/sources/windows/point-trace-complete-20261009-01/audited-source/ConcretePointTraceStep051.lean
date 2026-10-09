import ShielddSecurity.ConcretePointTraceStep050
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep051
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12946495741151266744237999923232381793408019015383148716798748428561357225791
def inputY : F := 15500199270983955706652284227911074337502088724272782586135594828494004060240
def doubleX : F := 43283353224862692608502734350572194950630919842954339706981640676510582507301
def doubleY : F := 22795852807091150677846287072000958073192823514865265462047845560519503582240
def doubleSlope : F := 12825408197009927758855242987793836772621264174488941335836605970137391614959
def addX : F := 18162287734678238101240760966422397591443200100057241259459337599027509260642
def addY : F := 21282273064572202846428430150050906084679599671700514532981454480643688385136
def addSlope : F := 15329628518002164307045280115773680441960626151608222802606487306587233616998
def outX : F := 18162287734678238101240760966422397591443200100057241259459337599027509260642
def outY : F := 21282273064572202846428430150050906084679599671700514532981454480643688385136

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2039432827017687 : Nat) • base) + ((2039432827017687 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep050.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15500199270983955706652284227911074337502088724272782586135594828494004060240 : Int)) * (38313629919321745095806618128845867494652027084611468554756980089420379085997 : Int) =
        (1 : Int) + (22651243888303836300664996695337082585994790855519162602183961900548757056543 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (12825408197009927758855242987793836772621264174488941335836605970137391614959 : Int) * ((2 : Int) * (15500199270983955706652284227911074337502088724272782586135594828494004060240 : Int)) =
        (3 : Int) * (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) + (-40964 : Int) * (-40964 : Int) + (-2007070350303551038254685871030071092532021517665311471184524563692437785411 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int) =
        (12825408197009927758855242987793836772621264174488941335836605970137391614959 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) - (12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) + (-3136995327541676469867216975199947051912021386299658818446292150250358907782 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (22795852807091150677846287072000958073192823514865265462047845560519503582240 : Int) =
        (12825408197009927758855242987793836772621264174488941335836605970137391614959 : Int) * ((12946495741151266744237999923232381793408019015383148716798748428561357225791 : Int) - (43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int)) - (15500199270983955706652284227911074337502088724272782586135594828494004060240 : Int) + (7420159944763964526060076587725616877083956832025083820850316778709791118890 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2039432827017687 : Nat) • base) + ((2039432827017687 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (8669430844381171043066351475142540448624906989794135127285077072822092460098 : Int) =
        (1 : Int) + (595721695471442961744668238184196843961522280236393622433340389416255628451 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (15329628518002164307045280115773680441960626151608222802606487306587233616998 : Int) * ((43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (22795852807091150677846287072000958073192823514865265462047845560519503582240 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1053378526874158823822513953534648879572066593473379041601437779137225115190 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) =
        (15329628518002164307045280115773680441960626151608222802606487306587233616998 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4481617017263404433487582229315068967897512809461623933030902658809502906642 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21282273064572202846428430150050906084679599671700514532981454480643688385136 : Int) =
        (15329628518002164307045280115773680441960626151608222802606487306587233616998 : Int) * ((43283353224862692608502734350572194950630919842954339706981640676510582507301 : Int) - (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int)) - (22795852807091150677846287072000958073192823514865265462047845560519503582240 : Int) + (-7344143692744322953509312322054527016546189482490084274939670568321436342562 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4078865654035375 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (4078865654035375 : Nat) = 2039432827017687 + 2039432827017687 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep051
