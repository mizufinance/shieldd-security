import ShielddSecurity.ConcretePointTraceStep036
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep037
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25039702515714292177706999073417860581340752207497498602037228781773638365500
def inputY : F := 4221612658970467990618803633932272602105282479425733521050182023217130092506
def doubleX : F := 40834565630342192016228737739210967477174351999593257180322308603735950747992
def doubleY : F := 45652122208100259904850644556775773780974873241917771571196409134802034168290
def doubleSlope : F := 37583812124400041551072090389865774520121334885262426148125790638448908488132
def outX : F := 40834565630342192016228737739210967477174351999593257180322308603735950747992
def outY : F := 45652122208100259904850644556775773780974873241917771571196409134802034168290

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((124477101258 : Nat) • base) + ((124477101258 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep036.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (4221612658970467990618803633932272602105282479425733521050182023217130092506 : Int)) * (13645611737487660126927384849274177904851506359360035105684054156270948697624 : Int) =
        (1 : Int) + (2197216583416556834734917343296622112339432423211200181011622847621391691999 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (37583812124400041551072090389865774520121334885262426148125790638448908488132 : Int) * ((2 : Int) * (4221612658970467990618803633932272602105282479425733521050182023217130092506 : Int)) =
        (3 : Int) * (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) + (-40964 : Int) * (-40964 : Int) + (-29819880128455833046705875301160686103540444695809595636516864854702498075824 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) =
        (37583812124400041551072090389865774520121334885262426148125790638448908488132 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) - (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) + (-26938483034460007642678211354436979948105043775462949931463269929786471510600 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45652122208100259904850644556775773780974873241917771571196409134802034168290 : Int) =
        (37583812124400041551072090389865774520121334885262426148125790638448908488132 : Int) * ((25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) - (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int)) - (4221612658970467990618803633932272602105282479425733521050182023217130092506 : Int) + (11321088202460090849258900730389885912255240756616718688156891274289979271980 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (248954202516 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (248954202516 : Nat) = 124477101258 + 124477101258 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep037
