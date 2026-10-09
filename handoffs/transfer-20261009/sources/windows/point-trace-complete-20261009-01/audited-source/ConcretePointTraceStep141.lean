import ShielddSecurity.ConcretePointTraceStep140
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep141
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22808718604705256063912135982558957704035991869959184213195827094148312579036
def inputY : F := 43720729742302932658189800306090436436144136875564719483920717754513938629189
def doubleX : F := 45043428021130317516632659685964965814148138165204161371089157438423368232874
def doubleY : F := 39054934539971930533322580504475241799334999252283357212945712780458120484372
def doubleSlope : F := 10176813642656768617163100351575093546249739056083352203306807187597577250090
def outX : F := 45043428021130317516632659685964965814148138165204161371089157438423368232874
def outY : F := 39054934539971930533322580504475241799334999252283357212945712780458120484372

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2524695553998170626929822179768754577165520 : Nat) • base) + ((2524695553998170626929822179768754577165520 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep140.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (43720729742302932658189800306090436436144136875564719483920717754513938629189 : Int)) * (12677769183121145219729032914355163368054454322539275536631742964860997409661 : Int) =
        (1 : Int) + (21141301383426458392739355818827366342339322944012772071590497312011177051489 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10176813642656768617163100351575093546249739056083352203306807187597577250090 : Int) * ((2 : Int) * (43720729742302932658189800306090436436144136875564719483920717754513938629189 : Int)) =
        (3 : Int) * (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) + (-40964 : Int) * (-40964 : Int) + (-12793483337670115805655564815323765664359607569580402048370522134898151817436 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int) =
        (10176813642656768617163100351575093546249739056083352203306807187597577250090 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) - (22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) + (-1975127440353925312953995616831833405005068219245233458274242065646666253194 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (39054934539971930533322580504475241799334999252283357212945712780458120484372 : Int) =
        (10176813642656768617163100351575093546249739056083352203306807187597577250090 : Int) * ((22808718604705256063912135982558957704035991869959184213195827094148312579036 : Int) - (45043428021130317516632659685964965814148138165204161371089157438423368232874 : Int)) - (43720729742302932658189800306090436436144136875564719483920717754513938629189 : Int) + (4315337416870699328831593772635931362849782852346662801702000742384041664037 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5049391107996341253859644359537509154331040 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (5049391107996341253859644359537509154331040 : Nat) = 2524695553998170626929822179768754577165520 + 2524695553998170626929822179768754577165520 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


set_option pp.all true in
#check @baseX
#print axioms baseX

set_option pp.all true in
#check @baseY
#print axioms baseY

set_option pp.all true in
#check @inputX
#print axioms inputX

set_option pp.all true in
#check @inputY
#print axioms inputY

set_option pp.all true in
#check @doubleX
#print axioms doubleX

set_option pp.all true in
#check @doubleY
#print axioms doubleY

set_option pp.all true in
#check @doubleSlope
#print axioms doubleSlope

set_option pp.all true in
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep141
