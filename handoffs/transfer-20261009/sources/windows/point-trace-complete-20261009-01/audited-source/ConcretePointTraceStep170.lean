import ShielddSecurity.ConcretePointTraceStep169
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep170
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3147633108254557659267076243015408644111025977049840848883617385222848040768
def inputY : F := 4699053524926918604632582460225994935048322750747739167969929053209420964540
def doubleX : F := 4574383873675073474997531814793264872383578656043479212721080342914275659164
def doubleY : F := 43057910871869432566862753009453045161447050598640654117845008102549832483525
def doubleSlope : F := 18118587774941238162609387213374305822165746212619014012999325860974882888900
def outX : F := 4574383873675073474997531814793264872383578656043479212721080342914275659164
def outY : F := 43057910871869432566862753009453045161447050598640654117845008102549832483525

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1355435604597343110811425393650279218947027233993522 : Nat) • base) + ((1355435604597343110811425393650279218947027233993522 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep169.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (4699053524926918604632582460225994935048322750747739167969929053209420964540 : Int)) * (42780977929753490300318726102425011339870353514800383302528161413086061059998 : Int) =
        (1 : Int) + (7667655187187215851492513403910259658164238999095954568609682151863410649103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (18118587774941238162609387213374305822165746212619014012999325860974882888900 : Int) * ((2 : Int) * (4699053524926918604632582460225994935048322750747739167969929053209420964540 : Int)) =
        (3 : Int) * (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) + (-40964 : Int) * (-40964 : Int) + (2680562581993593953427493530642046144939843338156113980383261468475517866960 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) =
        (18118587774941238162609387213374305822165746212619014012999325860974882888900 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) - (3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) + (-6260660699603933936485434402698581952700996900405466677712847745810582653436 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43057910871869432566862753009453045161447050598640654117845008102549832483525 : Int) =
        (18118587774941238162609387213374305822165746212619014012999325860974882888900 : Int) * ((3147633108254557659267076243015408644111025977049840848883617385222848040768 : Int) - (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int)) - (4699053524926918604632582460225994935048322750747739167969929053209420964540 : Int) + (492996615197125879140541565104895052938311957652309272387385541457200952305 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2710871209194686221622850787300558437894054467987044 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2710871209194686221622850787300558437894054467987044 : Nat) = 1355435604597343110811425393650279218947027233993522 + 1355435604597343110811425393650279218947027233993522 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep170
