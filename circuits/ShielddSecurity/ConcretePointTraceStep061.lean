import ShielddSecurity.ConcretePointTraceStep060
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep061
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25264546619036196760699080097025670586954124492301969447412186249824029563574
def inputY : F := 24531827071399617829178140171715396982852325552151936288704597559092994844304
def doubleX : F := 34042055887528668309919568744991815910690586088277638238387337863136485591305
def doubleY : F := 2624940459950538670799802193709391672391317389753127116179467863670286874285
def doubleSlope : F := 19363578416611014596169614439192832119718828490825218843852113542948818981637
def outX : F := 34042055887528668309919568744991815910690586088277638238387337863136485591305
def outY : F := 2624940459950538670799802193709391672391317389753127116179467863670286874285

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2088379214866112338 : Nat) • base) + ((2088379214866112338 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep060.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24531827071399617829178140171715396982852325552151936288704597559092994844304 : Int)) * (36513141753775769819328134585622197990669122286904869973148798183761303250917 : Int) =
        (1 : Int) + (34164932933627630801841731972320691346175866664284348813928148424531418209695 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19363578416611014596169614439192832119718828490825218843852113542948818981637 : Int) * ((2 : Int) * (24531827071399617829178140171715396982852325552151936288704597559092994844304 : Int)) =
        (3 : Int) * (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) + (-40964 : Int) * (-40964 : Int) + (-18400456366454898772894994576795955135955776647796950030840092682983131111228 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) =
        (19363578416611014596169614439192832119718828490825218843852113542948818981637 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) - (25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) + (-7150603815498185570716119644690141945030811519855488143449390905473044938668 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2624940459950538670799802193709391672391317389753127116179467863670286874285 : Int) =
        (19363578416611014596169614439192832119718828490825218843852113542948818981637 : Int) * ((25264546619036196760699080097025670586954124492301969447412186249824029563574 : Int) - (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int)) - (24531827071399617829178140171715396982852325552151936288704597559092994844304 : Int) + (3241368403890188858606940388912087273549713561074048294828749224479726366172 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4176758429732224676 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4176758429732224676 : Nat) = 2088379214866112338 + 2088379214866112338 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep061
