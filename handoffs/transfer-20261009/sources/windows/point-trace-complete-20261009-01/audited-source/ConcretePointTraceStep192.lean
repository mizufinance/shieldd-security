import ShielddSecurity.ConcretePointTraceStep191
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep192
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 17306150278911727178697492610024885255357294397587939352173410848272835446637
def inputY : F := 38542751348941648550757212862335065881563860355045139200178813676439229698953
def doubleX : F := 3247695854547107748213455149549234035978018092181694894252872548824707302566
def doubleY : F := 13074162549871009910548949283150339436620277388484112828409316766144365683819
def doubleSlope : F := 3359471813615877697960371427588879237606105634840296438254668458767558011863
def outX : F := 3247695854547107748213455149549234035978018092181694894252872548824707302566
def outY : F := 13074162549871009910548949283150339436620277388484112828409316766144365683819

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5685108978105054599048804774288940729146392115647965366317 : Nat) • base) + ((5685108978105054599048804774288940729146392115647965366317 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep191.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (38542751348941648550757212862335065881563860355045139200178813676439229698953 : Int)) * (14155867431547225838206110916500545139458837221255435637843117324191683636877 : Int) =
        (1 : Int) + (20810411830468430835324979948426129522420096124351180450638469722360203198697 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (3359471813615877697960371427588879237606105634840296438254668458767558011863 : Int) * ((2 : Int) * (38542751348941648550757212862335065881563860355045139200178813676439229698953 : Int)) =
        (3 : Int) * (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) + (-40964 : Int) * (-40964 : Int) + (-12196648510984648078965889822288091041600796155845149892944322617819867783261 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) =
        (3359471813615877697960371427588879237606105634840296438254668458767558011863 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) - (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) + (-215235291273125849146006292692922278042191625336732221246203922491171609369 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (13074162549871009910548949283150339436620277388484112828409316766144365683819 : Int) =
        (3359471813615877697960371427588879237606105634840296438254668458767558011863 : Int) * ((17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) - (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int)) - (38542751348941648550757212862335065881563860355045139200178813676439229698953 : Int) + (-900699782809388538474232203170374938115451430728611539662532810005018348077 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (11370217956210109198097609548577881458292784231295930732634 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (11370217956210109198097609548577881458292784231295930732634 : Nat) = 5685108978105054599048804774288940729146392115647965366317 + 5685108978105054599048804774288940729146392115647965366317 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep192
