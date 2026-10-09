import ShielddSecurity.ConcretePointTraceStep112
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep113
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4507714052907436369009784069803537723757080562639008376807807606686726018950
def inputY : F := 33944708627911101349340602174293675074636939729612380276147006734932065595466
def doubleX : F := 1187218077990636939514552056612861490503384585195403608129595451059979682121
def doubleY : F := 36685944280296316684503114723197426378612917856270484750074620125437188168126
def doubleSlope : F := 47933500971029891707286034883216666262253619036566512671628314456694004711
def outX : F := 1187218077990636939514552056612861490503384585195403608129595451059979682121
def outY : F := 36685944280296316684503114723197426378612917856270484750074620125437188168126

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((9405223853879312526173227205011079 : Nat) • base) + ((9405223853879312526173227205011079 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep112.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33944708627911101349340602174293675074636939729612380276147006734932065595466 : Int)) * (11561359368154797426177217980170610306086267277179997881247808182715667793415 : Int) =
        (1 : Int) + (14968644035553299647985445812358601771674756907957664276862041501299552361483 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (47933500971029891707286034883216666262253619036566512671628314456694004711 : Int) * ((2 : Int) * (33944708627911101349340602174293675074636939729612380276147006734932065595466 : Int)) =
        (3 : Int) * (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) + (-40964 : Int) * (-40964 : Int) + (-1100473298245929044962941694265871905704642672575870309199297144469746668688 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) =
        (47933500971029891707286034883216666262253619036566512671628314456694004711 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) - (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) + (-43817720361605353754080884262298931352073993726785157577717445726476836 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36685944280296316684503114723197426378612917856270484750074620125437188168126 : Int) =
        (47933500971029891707286034883216666262253619036566512671628314456694004711 : Int) * ((4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) - (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int)) - (33944708627911101349340602174293675074636939729612380276147006734932065595466 : Int) + (-3035383628220184767351805576094825722519794446986938218693151897766770179 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (18810447707758625052346454410022158 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (18810447707758625052346454410022158 : Nat) = 9405223853879312526173227205011079 + 9405223853879312526173227205011079 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep113
