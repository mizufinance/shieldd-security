import ShielddSecurity.ConcretePointTraceStep067
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep068
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44603938340258233252113140296809445244459209136115965877431219943072728940159
def inputY : F := 1524216170352971842545121194890977435737332366943269806145652212153043694917
def doubleX : F := 10721626244760493793223850252016159894508010638733582775465440128313675940066
def doubleY : F := 52407775636179615762342089679217248497425522703220290175166220734132236976569
def doubleSlope : F := 14700575666395987457757738603685506807526756329712587825602943072703748149304
def outX : F := 10721626244760493793223850252016159894508010638733582775465440128313675940066
def outY : F := 52407775636179615762342089679217248497425522703220290175166220734132236976569

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((267312539502862379270 : Nat) • base) + ((267312539502862379270 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep067.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1524216170352971842545121194890977435737332366943269806145652212153043694917 : Int)) * (41867337970678390918337119763494447861674421660007568454651325304339112890166 : Int) =
        (1 : Int) + (2434015769982327025202799576423858879809407837975704297826659241172306595611 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (14700575666395987457757738603685506807526756329712587825602943072703748149304 : Int) * ((2 : Int) * (1524216170352971842545121194890977435737332366943269806145652212153043694917 : Int)) =
        (3 : Int) * (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) + (-40964 : Int) * (-40964 : Int) + (-112970751728889838174273712563577119749970379195996476238735417503746542564083 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) =
        (14700575666395987457757738603685506807526756329712587825602943072703748149304 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) - (44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) + (-4121356308093960497127769919553294423009518474025410614957273729818983517800 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (52407775636179615762342089679217248497425522703220290175166220734132236976569 : Int) =
        (14700575666395987457757738603685506807526756329712587825602943072703748149304 : Int) * ((44603938340258233252113140296809445244459209136115965877431219943072728940159 : Int) - (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int)) - (1524216170352971842545121194890977435737332366943269806145652212153043694917 : Int) + (-9499021253078757666235443856443794277825287405760495802407437860617084146522 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (534625079005724758540 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (534625079005724758540 : Nat) = 267312539502862379270 + 267312539502862379270 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep068
