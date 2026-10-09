import ShielddSecurity.ConcretePointTraceStep084
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep085
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10980352158563505595411202311065466247344052636350715621156904004400508454
def inputY : F := 50884997764072393255343512754124160141563849760913156726834962519552580102715
def doubleX : F := 10378987859999056781139591117833698048571862064924587164826879234824060711809
def doubleY : F := 41718627792011559039542361908761065287226788854555695085040170064263241996038
def doubleSlope : F := 25264886148773021772482923153017462368532445019636437197753065714385300345046
def outX : F := 10378987859999056781139591117833698048571862064924587164826879234824060711809
def outY : F := 41718627792011559039542361908761065287226788854555695085040170064263241996038

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((35037189177719177775730294 : Nat) • base) + ((35037189177719177775730294 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep084.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (50884997764072393255343512754124160141563849760913156726834962519552580102715 : Int)) * (17846399817312068727299952069349114771529551642388323096807767780799197103370 : Int) =
        (1 : Int) + (34637126271573902337269745363610133666582757677036284874191441746352879508123 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25264886148773021772482923153017462368532445019636437197753065714385300345046 : Int) * ((2 : Int) * (50884997764072393255343512754124160141563849760913156726834962519552580102715 : Int)) =
        (3 : Int) * (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) + (-40964 : Int) * (-40964 : Int) + (49035264121900473676625730976688203156784533819086879640878921682133273367560 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) =
        (25264886148773021772482923153017462368532445019636437197753065714385300345046 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) - (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) + (-12173239599388964429666942697652377031553450786573256411057972323978849526559 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (41718627792011559039542361908761065287226788854555695085040170064263241996038 : Int) =
        (25264886148773021772482923153017462368532445019636437197753065714385300345046 : Int) * ((10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) - (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int)) - (50884997764072393255343512754124160141563849760913156726834962519552580102715 : Int) + (4995559402801244147546761222616698472863590781537469222728620856330149079891 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (70074378355438355551460588 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (70074378355438355551460588 : Nat) = 35037189177719177775730294 + 35037189177719177775730294 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep085
