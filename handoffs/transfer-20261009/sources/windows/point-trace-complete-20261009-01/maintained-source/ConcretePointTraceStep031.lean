import ShielddSecurity.ConcretePointTraceStep030
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep031
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 35904030519016117224290495438111213184051551672982889471995665290012844512132
def inputY : F := 16105951619558771069147932775113008581324909718474116609394308486113511240245
def doubleX : F := 25680312995057712136325629919018021145739081556782014044361090614908200595667
def doubleY : F := 16064879780612197845009179244966897833355462192413675642089857015121101354157
def doubleSlope : F := 25474178407829055838634760883747800532390891395364614037673870725443081820757
def outX : F := 25680312995057712136325629919018021145739081556782014044361090614908200595667
def outY : F := 16064879780612197845009179244966897833355462192413675642089857015121101354157

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1944954707 : Nat) • base) + ((1944954707 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep030.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16105951619558771069147932775113008581324909718474116609394308486113511240245 : Int)) * (37798627769545909688113405310824159197361250388071508641379534620822779088598 : Int) =
        (1 : Int) + (23220089990251679080242109262014968059451465460999678501901840208980701559963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25474178407829055838634760883747800532390891395364614037673870725443081820757 : Int) * ((2 : Int) * (16105951619558771069147932775113008581324909718474116609394308486113511240245 : Int)) =
        (3 : Int) * (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) + (-40964 : Int) * (-40964 : Int) + (-58103854324673874361373927423434081523807655554361885108534118980319725961422 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) =
        (25474178407829055838634760883747800532390891395364614037673870725443081820757 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) - (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) + (-12375759218027438737145640881571821341597555965312747669043789096814009272422 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (16064879780612197845009179244966897833355462192413675642089857015121101354157 : Int) =
        (25474178407829055838634760883747800532390891395364614037673870725443081820757 : Int) * ((35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) - (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int)) - (16105951619558771069147932775113008581324909718474116609394308486113511240245 : Int) + (-4966843851213321001976717335503912135671441748145538661701728407716487976931 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3889909414 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (3889909414 : Nat) = 1944954707 + 1944954707 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep031
