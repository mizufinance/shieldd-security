import ShielddSecurity.ConcretePointTraceStep124
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep125
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26212138188597492976639860102692701785350744286201968816696184634559745205319
def inputY : F := 1185202506295424070920956967281498296060393024609547071503116731031146342752
def doubleX : F := 25906469863109647471420343926081533993061111892883902574877023483720036516288
def doubleY : F := 18473219498009913267560376067107583509183964695431859210229355161621735750192
def doubleSlope : F := 13917419107472528937716361355004590324382334995200826976276864028392502820028
def outX : F := 25906469863109647471420343926081533993061111892883902574877023483720036516288
def outY : F := 18473219498009913267560376067107583509183964695431859210229355161621735750192

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((38523796905489664107205538631725381121 : Nat) • base) + ((38523796905489664107205538631725381121 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep124.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1185202506295424070920956967281498296060393024609547071503116731031146342752 : Int)) * (46499820838115347402412495983647353716164508647569351401663966113944291413824 : Int) =
        (1 : Int) + (2102061003675805107206354069905757930291076378793161734693026075476973449215 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13917419107472528937716361355004590324382334995200826976276864028392502820028 : Int) * ((2 : Int) * (1185202506295424070920956967281498296060393024609547071503116731031146342752 : Int)) =
        (3 : Int) * (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) + (-40964 : Int) * (-40964 : Int) + (-38680362222729537133811557599844537007917821663197025326162119586117057223091 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) =
        (13917419107472528937716361355004590324382334995200826976276864028392502820028 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) - (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) + (-3693931949569587877832687884146733527693401724322655468053061874216062099402 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (18473219498009913267560376067107583509183964695431859210229355161621735750192 : Int) =
        (13917419107472528937716361355004590324382334995200826976276864028392502820028 : Int) * ((26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) - (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int)) - (1185202506295424070920956967281498296060393024609547071503116731031146342752 : Int) + (-81129840581199671876402756034562884623743552946429946899466123836045024148 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (77047593810979328214411077263450762242 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (77047593810979328214411077263450762242 : Nat) = 38523796905489664107205538631725381121 + 38523796905489664107205538631725381121 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep125
