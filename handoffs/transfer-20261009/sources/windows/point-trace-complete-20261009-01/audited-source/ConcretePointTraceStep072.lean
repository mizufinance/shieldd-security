import ShielddSecurity.ConcretePointTraceStep071
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep072
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26296678237481069394708140462914653400357741769210537212673614898138334535806
def inputY : F := 5503274929932575530081370800506621385690094063178611928761524118590886654965
def doubleX : F := 34815630181111615896387691440911280968407745606240415350511026765795559601951
def doubleY : F := 33025881838446418669896895652124036313110170179930101567712181109501807640510
def doubleSlope : F := 29158122251610870985732527567722648946758712224418683668798351826786087767402
def outX : F := 34815630181111615896387691440911280968407745606240415350511026765795559601951
def outY : F := 33025881838446418669896895652124036313110170179930101567712181109501807640510

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4277000632045798068326 : Nat) • base) + ((4277000632045798068326 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep071.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (5503274929932575530081370800506621385690094063178611928761524118590886654965 : Int)) * (15632196337968117686668591723071931456460107770053929563553955425247970278516 : Int) =
        (1 : Int) + (3281275421424935673089643228438935022980273110422206529622921633245445746183 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (29158122251610870985732527567722648946758712224418683668798351826786087767402 : Int) * ((2 : Int) * (5503274929932575530081370800506621385690094063178611928761524118590886654965 : Int)) =
        (3 : Int) * (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) + (-40964 : Int) * (-40964 : Int) + (-33443048804614763020201238957978176997520073980577509647440183456822347712856 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) =
        (29158122251610870985732527567722648946758712224418683668798351826786087767402 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) - (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) + (-16214015507520113673278877084849599665504290019526209211107055671754186454993 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33025881838446418669896895652124036313110170179930101567712181109501807640510 : Int) =
        (29158122251610870985732527567722648946758712224418683668798351826786087767402 : Int) * ((26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) - (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int)) - (5503274929932575530081370800506621385690094063178611928761524118590886654965 : Int) + (4737150689263378599238417453342998537467622910418343658670449199832874221405 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (8554001264091596136652 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (8554001264091596136652 : Nat) = 4277000632045798068326 + 4277000632045798068326 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep072
