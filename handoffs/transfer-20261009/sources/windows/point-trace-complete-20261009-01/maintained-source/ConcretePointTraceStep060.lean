import ShielddSecurity.ConcretePointTraceStep059
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep060
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20725644920209728775432975754999927469548718699481902153929074922766755937601
def inputY : F := 8408705082890901898326845248907802312667179307170059442596528453140901587345
def doubleX : F := 25264546619036196760699080097025670586954124492301969447412186249824029563574
def doubleY : F := 24531827071399617829178140171715396982852325552151936288704597559092994844304
def doubleSlope : F := 16503999313965652628256130866062276892060934859604814057191031265690254335543
def outX : F := 25264546619036196760699080097025670586954124492301969447412186249824029563574
def outY : F := 24531827071399617829178140171715396982852325552151936288704597559092994844304

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1044189607433056169 : Nat) • base) + ((1044189607433056169 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep059.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8408705082890901898326845248907802312667179307170059442596528453140901587345 : Int)) * (42020355687469285829684903396800433518498230267870986242797978319933273589198 : Int) =
        (1 : Int) + (13476909740669977223260606501975783264402008702838914849025607785901977571163 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16503999313965652628256130866062276892060934859604814057191031265690254335543 : Int) * ((2 : Int) * (8408705082890901898326845248907802312667179307170059442596528453140901587345 : Int)) =
        (3 : Int) * (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) + (-40964 : Int) * (-40964 : Int) + (-19282648432208051441744801185282231419491647248428608736062605302843236414261 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) =
        (16503999313965652628256130866062276892060934859604814057191031265690254335543 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) - (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) + (-5194573227693309438702910440391558551884289160357691621946860552322307447457 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24531827071399617829178140171715396982852325552151936288704597559092994844304 : Int) =
        (16503999313965652628256130866062276892060934859604814057191031265690254335543 : Int) * ((20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) - (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int)) - (8408705082890901898326845248907802312667179307170059442596528453140901587345 : Int) + (1428602655594167582916985861409246592346187469389968235736500624126174059076 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2088379214866112338 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2088379214866112338 : Nat) = 1044189607433056169 + 1044189607433056169 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep060
