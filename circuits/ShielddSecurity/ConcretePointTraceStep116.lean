import ShielddSecurity.ConcretePointTraceStep115
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep116
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9561349938457233516426805880378293824940136867818816209920931006976062285907
def inputY : F := 17164809337310362779433859245001725753978060608604374250305735702192664356769
def doubleX : F := 12403692446580313785633390822410477115426175832151607827485173711655232651623
def doubleY : F := 33700085575931962137148683483736065078586451477817979566572420346354213946267
def doubleSlope : F := 5761027843022023024403252690110907370260044702429117376770393898377046507034
def outX : F := 12403692446580313785633390822410477115426175832151607827485173711655232651623
def outY : F := 33700085575931962137148683483736065078586451477817979566572420346354213946267

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((75241790831034500209385817640088635 : Nat) • base) + ((75241790831034500209385817640088635 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep115.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (17164809337310362779433859245001725753978060608604374250305735702192664356769 : Int)) * (27593219107510829953204182843217187314184870569494565037040557320341211653105 : Int) =
        (1 : Int) + (18065202245646042303088678394025485007829055820683889278883567603857366885153 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (5761027843022023024403252690110907370260044702429117376770393898377046507034 : Int) * ((2 : Int) * (17164809337310362779433859245001725753978060608604374250305735702192664356769 : Int)) =
        (3 : Int) * (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) + (-40964 : Int) * (-40964 : Int) + (-1458626344208920992024349096384189812275786008358894604481973044315441173223 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) =
        (5761027843022023024403252690110907370260044702429117376770393898377046507034 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) - (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) + (-632952948667841330188852778013047994890334201098087119308229116265558231199 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33700085575931962137148683483736065078586451477817979566572420346354213946267 : Int) =
        (5761027843022023024403252690110907370260044702429117376770393898377046507034 : Int) * ((9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) - (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int)) - (17164809337310362779433859245001725753978060608604374250305735702192664356769 : Int) + (312282655224371564658563773640033675748407056486547828670883356829051752260 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (150483581662069000418771635280177270 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (150483581662069000418771635280177270 : Nat) = 75241790831034500209385817640088635 + 75241790831034500209385817640088635 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep116
