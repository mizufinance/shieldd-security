import ShielddSecurity.ConcretePointOperationPilot02
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep003
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30820318921783750312400880173180348960265148459921400331265156797840279241074
def inputY : F := 7276904971089403592571761354287873523245317394885197382647934966827059832099
def doubleX : F := 47147054755274644194518790518054526068419522717362586263497422165601770954079
def doubleY : F := 20351905435684291711435317066650694346145484858116850191158012143203672964519
def doubleSlope : F := 23397647666184285804193182319666480047563427165728986714491186543683259438442
def outX : F := 47147054755274644194518790518054526068419522717362586263497422165601770954079
def outY : F := 20351905435684291711435317066650694346145484858116850191158012143203672964519

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((7 : Nat) • base) + ((7 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointOperationPilot02.prefix_seven
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7276904971089403592571761354287873523245317394885197382647934966827059832099 : Int)) * (17690919057468872711448067222925054494749455405735986791230363510613585970874 : Int) =
        (1 : Int) + (4910193122646806148942006103570108223606752616076348723219857048474349214427 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (23397647666184285804193182319666480047563427165728986714491186543683259438442 : Int) * ((2 : Int) * (7276904971089403592571761354287873523245317394885197382647934966827059832099 : Int)) =
        (3 : Int) * (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) + (-40964 : Int) * (-40964 : Int) + (-47851804698854944869027241656100996447802572338360186789358737079340548468288 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) =
        (23397647666184285804193182319666480047563427165728986714491186543683259438442 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) - (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) + (-10440369584421291790621463995715706352824011415706691326881687546664623337385 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20351905435684291711435317066650694346145484858116850191158012143203672964519 : Int) =
        (23397647666184285804193182319666480047563427165728986714491186543683259438442 : Int) * ((30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) - (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int)) - (7276904971089403592571761354287873523245317394885197382647934966827059832099 : Int) + (7285226217643009661597103300279705278210578126196471197275990632210712011756 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (14 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (14 : Nat) = 7 + 7 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep003
