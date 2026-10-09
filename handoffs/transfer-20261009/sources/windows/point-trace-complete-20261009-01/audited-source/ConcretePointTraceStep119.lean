import ShielddSecurity.ConcretePointTraceStep118
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep119
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11893770990643061008577527254443143771180603174341447628669045791696794618070
def inputY : F := 27446681108649409716288525877178956956600288735005894891603977269654924881142
def doubleX : F := 10767247375270118000210438247922729357708414268174687085759883470528384585428
def doubleY : F := 10327454339289633618115030706699013079743701626655483760299762745623047179222
def doubleSlope : F := 36837796178777267672578976355363281796469447891194603235740638199636934973534
def outX : F := 10767247375270118000210438247922729357708414268174687085759883470528384585428
def outY : F := 10327454339289633618115030706699013079743701626655483760299762745623047179222

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((601934326648276001675086541120709080 : Nat) • base) + ((601934326648276001675086541120709080 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep118.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (27446681108649409716288525877178956956600288735005894891603977269654924881142 : Int)) * (42688118523071535121613971254913846838995327236132069265222930836597121429016 : Int) =
        (1 : Int) + (44688762123942362365071228646836101124516008939151088321315025445586189473311 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36837796178777267672578976355363281796469447891194603235740638199636934973534 : Int) * ((2 : Int) * (27446681108649409716288525877178956956600288735005894891603977269654924881142 : Int)) =
        (3 : Int) * (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) + (-40964 : Int) * (-40964 : Int) + (30470839257642170164082112621231666212291749709574289681765639424100316182860 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int) =
        (36837796178777267672578976355363281796469447891194603235740638199636934973534 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) - (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) + (-25879671556485493440023750474957328249603105974560543776513510078457967321612 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (10327454339289633618115030706699013079743701626655483760299762745623047179222 : Int) =
        (36837796178777267672578976355363281796469447891194603235740638199636934973534 : Int) * ((11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) - (10767247375270118000210438247922729357708414268174687085759883470528384585428 : Int)) - (27446681108649409716288525877178956956600288735005894891603977269654924881142 : Int) + (-791417082199732410317632096110886127888382391767353061454463445184169247728 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1203868653296552003350173082241418160 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1203868653296552003350173082241418160 : Nat) = 601934326648276001675086541120709080 + 601934326648276001675086541120709080 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep119
