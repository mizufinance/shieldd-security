import ShielddSecurity.ConcretePointTraceStep103
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep104
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25288452322634376891223605381290424442664373563926490493860152509141197031420
def inputY : F := 35007192162067712850367973838231061448427204670773025696442100853824346579598
def doubleX : F := 39326180973746726893678134031361786199996369071432450876244551372792576949573
def doubleY : F := 23491918829854771203082160344717548861507358379830210409762103516625509777034
def doubleSlope : F := 8778152645660215197730146423303131287892329405844988854554527892078671751750
def outX : F := 39326180973746726893678134031361786199996369071432450876244551372792576949573
def outY : F := 23491918829854771203082160344717548861507358379830210409762103516625509777034

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((18369577839608032277682084384787 : Nat) • base) + ((18369577839608032277682084384787 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep103.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (35007192162067712850367973838231061448427204670773025696442100853824346579598 : Int)) * (10093370452010513382874607143085848479500987604949690826416797938265762486108 : Int) =
        (1 : Int) + (13477053936694132965724160736041199791287870866917642653988876102288617593359 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (8778152645660215197730146423303131287892329405844988854554527892078671751750 : Int) * ((2 : Int) * (35007192162067712850367973838231061448427204670773025696442100853824346579598 : Int)) =
        (3 : Int) * (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) + (-40964 : Int) * (-40964 : Int) + (-24866954261341506745171897691080683433662947511506746145763551090276446388952 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) =
        (8778152645660215197730146423303131287892329405844988854554527892078671751750 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) - (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) + (-1469527563202839118172910588610220503142528028311967927460418805947967831535 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (23491918829854771203082160344717548861507358379830210409762103516625509777034 : Int) =
        (8778152645660215197730146423303131287892329405844988854554527892078671751750 : Int) * ((25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) - (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int)) - (35007192162067712850367973838231061448427204670773025696442100853824346579598 : Int) + (2350019418695161105149450118435079689092946853357447494315795760494732422414 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (36739155679216064555364168769574 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (36739155679216064555364168769574 : Nat) = 18369577839608032277682084384787 + 18369577839608032277682084384787 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep104
