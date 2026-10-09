import ShielddSecurity.ConcretePointTraceStep035
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep036
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22609393211005250822101538537476652589974078742650691228624105849553002896316
def inputY : F := 49884585325894152805550737203374553372729977618737100674497782470942008989896
def doubleX : F := 25039702515714292177706999073417860581340752207497498602037228781773638365500
def doubleY : F := 4221612658970467990618803633932272602105282479425733521050182023217130092506
def doubleSlope : F := 49802406807720204211690347905730812245992601748457440032460741697795937263638
def outX : F := 25039702515714292177706999073417860581340752207497498602037228781773638365500
def outY : F := 4221612658970467990618803633932272602105282479425733521050182023217130092506

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((62238550629 : Nat) • base) + ((62238550629 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep035.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (49884585325894152805550737203374553372729977618737100674497782470942008989896 : Int)) * (25762927452883932979257691303610643594170757780320001334855418220204722049953 : Int) =
        (1 : Int) + (49018842480495191249347334069151463057476538011200220808456976673445467020175 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49802406807720204211690347905730812245992601748457440032460741697795937263638 : Int) * ((2 : Int) * (49884585325894152805550737203374553372729977618737100674497782470942008989896 : Int)) =
        (3 : Int) * (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) + (-40964 : Int) * (-40964 : Int) + (65512224752362068627682638918609431246657742256971429009896336039170037147616 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int) =
        (49802406807720204211690347905730812245992601748457440032460741697795937263638 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) - (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) + (-47301198188415414020809367778015995657628405167782697863570310654142418229560 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (4221612658970467990618803633932272602105282479425733521050182023217130092506 : Int) =
        (49802406807720204211690347905730812245992601748457440032460741697795937263638 : Int) * ((22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) - (25039702515714292177706999073417860581340752207497498602037228781773638365500 : Int)) - (49884585325894152805550737203374553372729977618737100674497782470942008989896 : Int) + (2308252742182175999880010727863264277588096955086811503719732783469610527138 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (124477101258 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (124477101258 : Nat) = 62238550629 + 62238550629 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep036
