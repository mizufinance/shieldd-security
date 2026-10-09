import ShielddSecurity.ConcretePointTraceStep247
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep248
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 36638997471878153231161387444176692100234888765923289061450903936609426886618
def inputY : F := 7160036431361236381630122941922975820061908871623977661743934136708218947086
def doubleX : F := 11461277467152783638462415397995436491772411768632117744545883083797289909445
def doubleY : F := 37938685389307505719446694593178758230543244701943533122566970596180847459634
def doubleSlope : F := 26159469056414459492662617089041568450541914156212143550268755980286910453464
def outX : F := 11461277467152783638462415397995436491772411768632117744545883083797289909445
def outY : F := 37938685389307505719446694593178758230543244701943533122566970596180847459634

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((409655274805673363120685472720202858106620079117019830085334947649511453387 : Nat) • base) + ((409655274805673363120685472720202858106620079117019830085334947649511453387 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep247.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7160036431361236381630122941922975820061908871623977661743934136708218947086 : Int)) * (37302778692682377309260501481486516034407561752078597654904152556484282274250 : Int) =
        (1 : Int) + (10187271730988848784621733015381322775291381130983395252078352282572745894423 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (26159469056414459492662617089041568450541914156212143550268755980286910453464 : Int) * ((2 : Int) * (7160036431361236381630122941922975820061908871623977661743934136708218947086 : Int)) =
        (3 : Int) * (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) + (-40964 : Int) * (-40964 : Int) + (-69659234104432048838591034677848534626622661417050001601414342279179677217724 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) =
        (26159469056414459492662617089041568450541914156212143550268755980286910453464 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) - (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) + (-13050565457866580836953215843497186848702830501271717915370839639170543434191 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (37938685389307505719446694593178758230543244701943533122566970596180847459634 : Int) =
        (26159469056414459492662617089041568450541914156212143550268755980286910453464 : Int) * ((36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) - (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int)) - (7160036431361236381630122941922975820061908871623977661743934136708218947086 : Int) + (-12560785629589629007981819771071793756273361845197611908520890920090039952504 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) = 409655274805673363120685472720202858106620079117019830085334947649511453387 + 409655274805673363120685472720202858106620079117019830085334947649511453387 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep248
