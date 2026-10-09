import ShielddSecurity.ConcretePointTraceStep141
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep142
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45043428021130317516632659685964965814148138165204161371089157438423368232874
def inputY : F := 39054934539971930533322580504475241799334999252283357212945712780458120484372
def doubleX : F := 44663576030515940103235526833984529565071887642337226235294731248161077879817
def doubleY : F := 5113416331361045646387677331787344439733296610656969557547007770076282950534
def doubleSlope : F := 49639654805152241141072841915148119065422778790348434298039711103490444228504
def addX : F := 36619481870374698177242339535765999636530294886257028529188103025204578161488
def addY : F := 37608226641050498246563775203336926750468533856932426711139792756585177220237
def addSlope : F := 28628092346056518616244679593105395095084669462011559382526484165313925236299
def outX : F := 36619481870374698177242339535765999636530294886257028529188103025204578161488
def outY : F := 37608226641050498246563775203336926750468533856932426711139792756585177220237

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5049391107996341253859644359537509154331040 : Nat) • base) + ((5049391107996341253859644359537509154331040 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep141.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (39054934539971930533322580504475241799334999252283357212945712780458120484372 : Int)) * (6981442747704106975975986277245918641734675638096242503621444960016112019883 : Int) =
        (1 : Int) + (10399742107689136844466959178501806994815295743432487551558719490483016492727 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49639654805152241141072841915148119065422778790348434298039711103490444228504 : Int) * ((2 : Int) * (39054934539971930533322580504475241799334999252283357212945712780458120484372 : Int)) =
        (3 : Int) * (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) + (-40964 : Int) * (-40964 : Int) + (-42134974925111066099274252868568834117357207743041735308254036350792154008668 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int) =
        (49639654805152241141072841915148119065422778790348434298039711103490444228504 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) - (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) + (-46992547009944017232993922604908818350123513973379150063492494110409734563563 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (5113416331361045646387677331787344439733296610656969557547007770076282950534 : Int) =
        (49639654805152241141072841915148119065422778790348434298039711103490444228504 : Int) * ((45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) - (44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int)) - (39054934539971930533322580504475241799334999252283357212945712780458120484372 : Int) + (-359595823053834367554137274599983020450983343543454243543249522307074135294 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((5049391107996341253859644359537509154331040 : Nat) • base) + ((5049391107996341253859644359537509154331040 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (39707172684553406886472404548720898081304557502830388479330744978861772807740 : Int) =
        (1 : Int) + (3773662924361303989928162895096770480768392060634625678475625192674601016743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (28628092346056518616244679593105395095084669462011559382526484165313925236299 : Int) * ((44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (5113416331361045646387677331787344439733296610656969557547007770076282950534 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (2720736919240065210176858803477177644179518973888136877174623707871594158006 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int) =
        (28628092346056518616244679593105395095084669462011559382526484165313925236299 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-15629903546706035864766398763636584679772332296686042535497963596907705170837 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (37608226641050498246563775203336926750468533856932426711139792756585177220237 : Int) =
        (28628092346056518616244679593105395095084669462011559382526484165313925236299 : Int) * ((44663576030515940103235526833984529565071887642337226235294731248161077879817 : Int) - (36619481870374698177242339535765999636530294886257028529188103025204578161488 : Int)) - (5113416331361045646387677331787344439733296610656969557547007770076282950534 : Int) + (-4391784626227385665518609419186023543386718665008863210414221830814987527200 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (10098782215992682507719288719075018308662081 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (10098782215992682507719288719075018308662081 : Nat) = 5049391107996341253859644359537509154331040 + 5049391107996341253859644359537509154331040 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep142
