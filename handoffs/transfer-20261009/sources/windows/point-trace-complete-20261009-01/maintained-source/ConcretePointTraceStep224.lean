import ShielddSecurity.ConcretePointTraceStep223
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep224
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15181243147482961138848927792205229419202939875801041645726413033511828683555
def inputY : F := 22621897723724176282109242261266287259090309777626480277263534638136596413319
def doubleX : F := 35855311103515762529636146932706375161657747231140237833757407643560208830105
def doubleY : F := 12992391665349874243395288362958038728209139763959198044342396570649696549698
def doubleSlope : F := 29893102702710137652994002141691664706518941780380853383682020498918671519770
def outX : F := 35855311103515762529636146932706375161657747231140237833757407643560208830105
def outY : F := 12992391665349874243395288362958038728209139763959198044342396570649696549698

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((24417357135157189555209009213459662086166148133100261097272333362669 : Nat) • base) + ((24417357135157189555209009213459662086166148133100261097272333362669 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep223.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (22621897723724176282109242261266287259090309777626480277263534638136596413319 : Int)) * (5052537069237539421972908451972024767800248932114081448295547539729058041961 : Int) =
        (1 : Int) + (4359533485190529123107704717284743736410968411804455030073834428282132280509 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (29893102702710137652994002141691664706518941780380853383682020498918671519770 : Int) * ((2 : Int) * (22621897723724176282109242261266287259090309777626480277263534638136596413319 : Int)) =
        (3 : Int) * (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) + (-40964 : Int) * (-40964 : Int) + (12607150948737778431245250707455439227181049191773585304237130064620669252913 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) =
        (29893102702710137652994002141691664706518941780380853383682020498918671519770 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) - (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) + (-17041721649735497780140238143920669800378593233842123192431151908198342917581 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (12992391665349874243395288362958038728209139763959198044342396570649696549698 : Int) =
        (29893102702710137652994002141691664706518941780380853383682020498918671519770 : Int) * ((15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) - (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int)) - (22621897723724176282109242261266287259090309777626480277263534638136596413319 : Int) + (11786053625088749151290573262065822417548414804657365372461619886801196634309 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (48834714270314379110418018426919324172332296266200522194544666725338 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (48834714270314379110418018426919324172332296266200522194544666725338 : Nat) = 24417357135157189555209009213459662086166148133100261097272333362669 + 24417357135157189555209009213459662086166148133100261097272333362669 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep224
