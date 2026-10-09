import ShielddSecurity.ConcretePointTraceStep041
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep042
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44450694463824942691575793701650651308473417017582019429283436299952812774218
def inputY : F := 505628977924477309014895360288863992981718296654362585135936923774803781498
def doubleX : F := 14736059063133226005475270759437344504666805279928376054533887584687287264472
def doubleY : F := 46093445731598237104436406547841093029204247362269075774799967223344946138703
def doubleSlope : F := 31875989980079412763069416781133294566903659109303957043334503062307382393285
def addX : F := 2773412723143448389350708801469384239684308280547399336978566097928962106716
def addY : F := 40503156611042317495852284948043867079457983042714828037865598012630344930635
def addSlope : F := 31354321697780988543806890915106825023298199867887296941991794361044278990783
def outX : F := 2773412723143448389350708801469384239684308280547399336978566097928962106716
def outY : F := 40503156611042317495852284948043867079457983042714828037865598012630344930635

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3983267240268 : Nat) • base) + ((3983267240268 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep041.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (505628977924477309014895360288863992981718296654362585135936923774803781498 : Int)) * (45417792232981133467113664026666672813288648885839714600360107533221436169627 : Int) =
        (1 : Int) + (875909929591186565839065717352025838468945736536755686301085789819374629307 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (31875989980079412763069416781133294566903659109303957043334503062307382393285 : Int) * ((2 : Int) * (505628977924477309014895360288863992981718296654362585135936923774803781498 : Int)) =
        (3 : Int) * (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) + (-40964 : Int) * (-40964 : Int) + (-112429855452810181581093287796367874989001488338004039468182946670709851548120 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int) =
        (31875989980079412763069416781133294566903659109303957043334503062307382393285 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) - (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) + (-19377548936040578998289122738407372173613435151623218352050948007711579080245 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (46093445731598237104436406547841093029204247362269075774799967223344946138703 : Int) =
        (31875989980079412763069416781133294566903659109303957043334503062307382393285 : Int) * ((44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) - (14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int)) - (505628977924477309014895360288863992981718296654362585135936923774803781498 : Int) + (-18063652358823869034511084947427708410294826252455711941200091712396451178993 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3983267240268 : Nat) • base) + ((3983267240268 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (11169189208721902362391249635476933689257112201996175399517868400973531982315 : Int) =
        (1 : Int) + (-5313269907286714945442964737168971295057980243319279829600944110584911363882 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (31354321697780988543806890915106825023298199867887296941991794361044278990783 : Int) * ((14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (46093445731598237104436406547841093029204247362269075774799967223344946138703 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-14915493938460201383589504570655406353495182675758995765743538472547572955690 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) =
        (31354321697780988543806890915106825023298199867887296941991794361044278990783 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-18748490148101620026737456467414997046827265526273901953960742079242969280322 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (40503156611042317495852284948043867079457983042714828037865598012630344930635 : Int) =
        (31354321697780988543806890915106825023298199867887296941991794361044278990783 : Int) * ((14736059063133226005475270759437344504666805279928376054533887584687287264472 : Int) - (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int)) - (46093445731598237104436406547841093029204247362269075774799967223344946138703 : Int) + (-7153130570399012241457716813409379352030370064619514597586998624082288532970 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (7966534480537 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (7966534480537 : Nat) = 3983267240268 + 3983267240268 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep042
