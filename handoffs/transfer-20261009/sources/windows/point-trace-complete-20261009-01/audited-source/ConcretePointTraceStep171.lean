import ShielddSecurity.ConcretePointTraceStep170
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep171
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4574383873675073474997531814793264872383578656043479212721080342914275659164
def inputY : F := 43057910871869432566862753009453045161447050598640654117845008102549832483525
def doubleX : F := 1768503296666626415548150318257779985916935307768164737224397343752491127180
def doubleY : F := 33148334770121454971270983107082426799765682846177826899308707417511807605290
def doubleSlope : F := 36550502547156721689474339315531339414484940203337961541813549486979907681435
def outX : F := 1768503296666626415548150318257779985916935307768164737224397343752491127180
def outY : F := 33148334770121454971270983107082426799765682846177826899308707417511807605290

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2710871209194686221622850787300558437894054467987044 : Nat) • base) + ((2710871209194686221622850787300558437894054467987044 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep170.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (43057910871869432566862753009453045161447050598640654117845008102549832483525 : Int)) * (35224003778102221924234355445244923927708992260814693143527713492249622243648 : Int) =
        (1 : Int) + (57848639320408469005594425541562123433866484563226376136543700179058019204223 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36550502547156721689474339315531339414484940203337961541813549486979907681435 : Int) * ((2 : Int) * (43057910871869432566862753009453045161447050598640654117845008102549832483525 : Int)) =
        (3 : Int) * (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) + (-40964 : Int) * (-40964 : Int) + (58829982110933310900111488214464989225945948277767083028993630226800952338190 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int) =
        (36550502547156721689474339315531339414484940203337961541813549486979907681435 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) - (4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) + (-25477580606558360396770443933890918731765504859756531542650704832664047606045 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33148334770121454971270983107082426799765682846177826899308707417511807605290 : Int) =
        (36550502547156721689474339315531339414484940203337961541813549486979907681435 : Int) * ((4574383873675073474997531814793264872383578656043479212721080342914275659164 : Int) - (1768503296666626415548150318257779985916935307768164737224397343752491127180 : Int)) - (43057910871869432566862753009453045161447050598640654117845008102549832483525 : Int) + (-1955843109978530218202628217571940197943927861008209797183593089701449285825 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5421742418389372443245701574601116875788108935974088 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (5421742418389372443245701574601116875788108935974088 : Nat) = 2710871209194686221622850787300558437894054467987044 + 2710871209194686221622850787300558437894054467987044 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep171
