import ShielddSecurity.ConcretePointTraceStep213
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep214
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39682198076745101127618121360848096854785234192298571090071992487594601234210
def inputY : F := 43542419052801681150733911933397873859937677169140860421067672362058738362163
def doubleX : F := 5254431352040567715800818809815540178997839561488166687536101363101735459962
def doubleY : F := 45089967721278676411666858878152654011380270001749389418729351942356335091858
def doubleSlope : F := 38036436326426637701047396346833440628239701857480013066407917350236730670101
def outX : F := 5254431352040567715800818809815540178997839561488166687536101363101735459962
def outY : F := 45089967721278676411666858878152654011380270001749389418729351942356335091858

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((23845075327301942925008798060019201256021629036230723727805013049 : Nat) • base) + ((23845075327301942925008798060019201256021629036230723727805013049 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep213.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (43542419052801681150733911933397873859937677169140860421067672362058738362163 : Int)) * (33695725990948551699572219458081742607202644961428016897499077733553894042024 : Int) =
        (1 : Int) + (55961435428935114566010218657735105601170492161390018093330194500790305605871 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (38036436326426637701047396346833440628239701857480013066407917350236730670101 : Int) * ((2 : Int) * (43542419052801681150733911933397873859937677169140860421067672362058738362163 : Int)) =
        (3 : Int) * (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) + (-40964 : Int) * (-40964 : Int) + (-26921141838303382291431733632846705177231949485579643014219987967546040285470 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) =
        (38036436326426637701047396346833440628239701857480013066407917350236730670101 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) - (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) + (-27591233741829620997873742341130490192618037467883397764606073954766309424899 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45089967721278676411666858878152654011380270001749389418729351942356335091858 : Int) =
        (38036436326426637701047396346833440628239701857480013066407917350236730670101 : Int) * ((39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) - (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int)) - (43542419052801681150733911933397873859937677169140860421067672362058738362163 : Int) + (-24973542493794036617392110996141871972015294134910129178282647418501675544579 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (47690150654603885850017596120038402512043258072461447455610026098 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (47690150654603885850017596120038402512043258072461447455610026098 : Nat) = 23845075327301942925008798060019201256021629036230723727805013049 + 23845075327301942925008798060019201256021629036230723727805013049 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep214
