import ShielddSecurity.ConcretePointTraceStep040
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep041
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22561686791837315817037399241635204036369276912016019155388527301707957439202
def inputY : F := 29329951215706315745250086554306724329676745546537473139115404775551773893853
def doubleX : F := 44450694463824942691575793701650651308473417017582019429283436299952812774218
def doubleY : F := 505628977924477309014895360288863992981718296654362585135936923774803781498
def doubleSlope : F := 31051013147940506890597115625904645919738546260742830783878617772953562932009
def outX : F := 44450694463824942691575793701650651308473417017582019429283436299952812774218
def outY : F := 505628977924477309014895360288863992981718296654362585135936923774803781498

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1991633620134 : Nat) • base) + ((1991633620134 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep040.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29329951215706315745250086554306724329676745546537473139115404775551773893853 : Int)) * (32563282923801379617580025006131955910521858398111019026920652387463966404780 : Int) =
        (1 : Int) + (36428475595707973136883771936140484443947073037246736505101539562962456897783 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (31051013147940506890597115625904645919738546260742830783878617772953562932009 : Int) * ((2 : Int) * (29329951215706315745250086554306724329676745546537473139115404775551773893853 : Int)) =
        (3 : Int) * (22561686791837315817037399241635204036369276912016019155388527301707957439202 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22561686791837315817037399241635204036369276912016019155388527301707957439202 : Int) + (-40964 : Int) * (-40964 : Int) + (5613719004263636845825956295026754751130266847734127606845558501896046353486 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int) =
        (31051013147940506890597115625904645919738546260742830783878617772953562932009 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22561686791837315817037399241635204036369276912016019155388527301707957439202 : Int) - (22561686791837315817037399241635204036369276912016019155388527301707957439202 : Int) + (-18387514545975228837839758482022434232334688499676898419776767507604647351179 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (505628977924477309014895360288863992981718296654362585135936923774803781498 : Int) =
        (31051013147940506890597115625904645919738546260742830783878617772953562932009 : Int) * ((22561686791837315817037399241635204036369276912016019155388527301707957439202 : Int) - (44450694463824942691575793701650651308473417017582019429283436299952812774218 : Int)) - (29329951215706315745250086554306724329676745546537473139115404775551773893853 : Int) + (12962039114409092959627369246025211090969496041864300144557172774210315279615 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3983267240268 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (3983267240268 : Nat) = 1991633620134 + 1991633620134 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep041
