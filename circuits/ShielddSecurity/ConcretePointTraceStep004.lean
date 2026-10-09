import ShielddSecurity.ConcretePointTraceStep003
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep004
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 47147054755274644194518790518054526068419522717362586263497422165601770954079
def inputY : F := 20351905435684291711435317066650694346145484858116850191158012143203672964519
def doubleX : F := 27416318839537145010600649894766761814387953753752631843700945536134826640529
def doubleY : F := 1470886311888350237318958292419739516514468566140978908671109266579203296049
def doubleSlope : F := 25587919634162511807537978118539981961076459397255509781783998833764671297937
def outX : F := 27416318839537145010600649894766761814387953753752631843700945536134826640529
def outY : F := 1470886311888350237318958292419739516514468566140978908671109266579203296049

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((14 : Nat) • base) + ((14 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep003.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (20351905435684291711435317066650694346145484858116850191158012143203672964519 : Int)) * (16353817314070558495655131089794865911804032113190299408323613534640503815558 : Int) =
        (1 : Int) + (12694795018747181687507772260098450443775322535206877721226356933067881554131 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25587919634162511807537978118539981961076459397255509781783998833764671297937 : Int) * ((2 : Int) * (20351905435684291711435317066650694346145484858116850191158012143203672964519 : Int)) =
        (3 : Int) * (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) + (-40964 : Int) * (-40964 : Int) + (-107312187621865603177398104173089280296176610825841885985637806012918450860213 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) =
        (25587919634162511807537978118539981961076459397255509781783998833764671297937 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) - (47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) + (-12486520517062842979182904812025259469605833696258058571515016273155092473050 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1470886311888350237318958292419739516514468566140978908671109266579203296049 : Int) =
        (25587919634162511807537978118539981961076459397255509781783998833764671297937 : Int) * ((47147054755274644194518790518054526068419522717362586263497422165601770954079 : Int) - (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int)) - (20351905435684291711435317066650694346145484858116850191158012143203672964519 : Int) + (-9628302822230143169657770808921830206998182858267625474161966633031472800214 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (28 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (28 : Nat) = 14 + 14 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep004
