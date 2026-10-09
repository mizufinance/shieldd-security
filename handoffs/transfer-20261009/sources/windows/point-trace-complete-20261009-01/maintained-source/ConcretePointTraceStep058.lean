import ShielddSecurity.ConcretePointTraceStep057
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep058
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 23229236759624610526295678402042587186482520209982066668198783466454158179698
def inputY : F := 3406172924223861995638869373785609199177078749959398644831399006410667753524
def doubleX : F := 9748009729789797770934086729667614535774896700998054132724512323837044997140
def doubleY : F := 33007109801971083240139360097564809980050493546141416887888037303055264752138
def doubleSlope : F := 48296306737734008648344039602554617631880948706889799089221589052778629780945
def outX : F := 9748009729789797770934086729667614535774896700998054132724512323837044997140
def outY : F := 33007109801971083240139360097564809980050493546141416887888037303055264752138

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((261047401858264042 : Nat) • base) + ((261047401858264042 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep057.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3406172924223861995638869373785609199177078749959398644831399006410667753524 : Int)) * (2562862493233304937100512554217663864350537700145179510061977278497581942532 : Int) =
        (1 : Int) + (332961080703050771379246919567435103245912763938165575498257555320369633695 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (48296306737734008648344039602554617631880948706889799089221589052778629780945 : Int) * ((2 : Int) * (3406172924223861995638869373785609199177078749959398644831399006410667753524 : Int)) =
        (3 : Int) * (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) + (-40964 : Int) * (-40964 : Int) + (-24597304274912805771606497023635532903423026271598108797940797320330010157140 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) =
        (48296306737734008648344039602554617631880948706889799089221589052778629780945 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) - (23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) + (-44483537973096832207897842451324533788917706050047949204343510353733773229489 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33007109801971083240139360097564809980050493546141416887888037303055264752138 : Int) =
        (48296306737734008648344039602554617631880948706889799089221589052778629780945 : Int) * ((23229236759624610526295678402042587186482520209982066668198783466454158179698 : Int) - (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int)) - (3406172924223861995638869373785609199177078749959398644831399006410667753524 : Int) + (-12416946864325241121066221148138709987536874310077796863242457881861771456896 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (522094803716528084 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (522094803716528084 : Nat) = 261047401858264042 + 261047401858264042 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep058
