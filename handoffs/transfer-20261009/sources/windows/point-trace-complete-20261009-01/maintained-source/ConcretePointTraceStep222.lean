import ShielddSecurity.ConcretePointTraceStep221
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep222
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41166441787998895917461425299633054061526863280062283667716671165737095590783
def inputY : F := 33716406380140631984492975456332915229715017469525544957878853284288154815086
def doubleX : F := 41947726929964311439622386140736546154831328010705607939974728641541653178062
def doubleY : F := 24011830238690429127330354905040574902778815943680823329702414212912642775825
def doubleSlope : F := 22540113177955937615697313612524197108350197369831818788621498379826496492322
def outX : F := 41947726929964311439622386140736546154831328010705607939974728641541653178062
def outY : F := 24011830238690429127330354905040574902778815943680823329702414212912642775825

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((6104339283789297388802252303364915521541537033275065274318083340667 : Nat) • base) + ((6104339283789297388802252303364915521541537033275065274318083340667 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep221.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33716406380140631984492975456332915229715017469525544957878853284288154815086 : Int)) * (24901267290974993780091278727368228255412033209557560521359174877847769129955 : Int) =
        (1 : Int) + (32023161416071320575485618446632384836099570892249829981984869337695671751443 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22540113177955937615697313612524197108350197369831818788621498379826496492322 : Int) * ((2 : Int) * (33716406380140631984492975456332915229715017469525544957878853284288154815086 : Int)) =
        (3 : Int) * (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) + (-40964 : Int) * (-40964 : Int) + (-67970345589275786717584010913168071619964957140343364767818325130629864176107 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) =
        (22540113177955937615697313612524197108350197369831818788621498379826496492322 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) - (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) + (-9689105033114196412691105270734331705266783016982509225838824974218524115648 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24011830238690429127330354905040574902778815943680823329702414212912642775825 : Int) =
        (22540113177955937615697313612524197108350197369831818788621498379826496492322 : Int) * ((41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) - (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int)) - (33716406380140631984492975456332915229715017469525544957878853284288154815086 : Int) + (335843646460382696842523946851558743237595057817421419373824739006265234173 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (12208678567578594777604504606729831043083074066550130548636166681334 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (12208678567578594777604504606729831043083074066550130548636166681334 : Nat) = 6104339283789297388802252303364915521541537033275065274318083340667 + 6104339283789297388802252303364915521541537033275065274318083340667 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep222
