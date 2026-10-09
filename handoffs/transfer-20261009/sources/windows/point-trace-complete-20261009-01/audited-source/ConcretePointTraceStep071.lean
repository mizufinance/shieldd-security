import ShielddSecurity.ConcretePointTraceStep070
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep071
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 38529391522479304756200082598569073750811623681082017512231479574297404564283
def inputY : F := 8099763043621779494306834975162922283230112941265954589158892124384291713435
def doubleX : F := 26296678237481069394708140462914653400357741769210537212673614898138334535806
def doubleY : F := 5503274929932575530081370800506621385690094063178611928761524118590886654965
def doubleSlope : F := 51259369849055224448751316047710402589698747408892790159264001585089077360305
def outX : F := 26296678237481069394708140462914653400357741769210537212673614898138334535806
def outY : F := 5503274929932575530081370800506621385690094063178611928761524118590886654965

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2138500316022899034163 : Nat) • base) + ((2138500316022899034163 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep070.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8099763043621779494306834975162922283230112941265954589158892124384291713435 : Int)) * (22996667903030847547859854566314025568900164268117920399585855013156080566462 : Int) =
        (1 : Int) + (7104584797538440540223973294976057585935501536943618449827172735630731190803 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (51259369849055224448751316047710402589698747408892790159264001585089077360305 : Int) * ((2 : Int) * (8099763043621779494306834975162922283230112941265954589158892124384291713435 : Int)) =
        (3 : Int) * (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) + (-40964 : Int) * (-40964 : Int) + (-69097054680433202507628022066496516717512088019626815694913859649946280320725 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int) =
        (51259369849055224448751316047710402589698747408892790159264001585089077360305 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) - (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) + (-50109261808767140729144587649856854413507020383609442576995476697099736416117 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (5503274929932575530081370800506621385690094063178611928761524118590886654965 : Int) =
        (51259369849055224448751316047710402589698747408892790159264001585089077360305 : Int) * ((38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) - (26296678237481069394708140462914653400357741769210537212673614898138334535806 : Int)) - (8099763043621779494306834975162922283230112941265954589158892124384291713435 : Int) + (-11958247524981198477086932089448479862186492738627068326230893452947110518045 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4277000632045798068326 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4277000632045798068326 : Nat) = 2138500316022899034163 + 2138500316022899034163 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep071
