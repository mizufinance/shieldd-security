import ShielddSecurity.ConcretePointTraceStep015
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep016
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 46036438912242758694663670900035586573714113806566576077092645583543283979915
def inputY : F := 24294495313598841576630948218175267399274674983910386354687952540563966479383
def doubleX : F := 31351039174741370791392834605725171092213821371365588115107764312007852760660
def doubleY : F := 48978444531009348041142931747681118351514905800360769278864904733304207524679
def doubleSlope : F := 21591681359449306021691927676341934797176707651389472953734518701163337348512
def outX : F := 31351039174741370791392834605725171092213821371365588115107764312007852760660
def outY : F := 48978444531009348041142931747681118351514905800360769278864904733304207524679

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((59355 : Nat) • base) + ((59355 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep015.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24294495313598841576630948218175267399274674983910386354687952540563966479383 : Int)) * (9311131263348419569054149491968304658388638771330943993743341644755121851118 : Int) =
        (1 : Int) + (8628033158070673991066873595236408649745083598624912572821726319270581487299 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (21591681359449306021691927676341934797176707651389472953734518701163337348512 : Int) * ((2 : Int) * (24294495313598841576630948218175267399274674983910386354687952540563966479383 : Int)) =
        (3 : Int) * (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) + (-40964 : Int) * (-40964 : Int) + (-101246390991498886824654701644032236690016602344665849136277957299794317902603 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) =
        (21591681359449306021691927676341934797176707651389472953734518701163337348512 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) - (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) + (-8890872944734228673388419477004423382564153971274606967547209083914665793694 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (48978444531009348041142931747681118351514905800360769278864904733304207524679 : Int) =
        (21591681359449306021691927676341934797176707651389472953734518701163337348512 : Int) * ((46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) - (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int)) - (24294495313598841576630948218175267399274674983910386354687952540563966479383 : Int) + (-6047052151018234026271517403902804971297332740745827600739921439555916281346 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (118710 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (118710 : Nat) = 59355 + 59355 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep016
