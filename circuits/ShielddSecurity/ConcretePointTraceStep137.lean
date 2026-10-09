import ShielddSecurity.ConcretePointTraceStep136
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep137
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 24540671909485615994786041396287502347304589168921219187529425981708797037995
def inputY : F := 21950383374920738125391128671308417804121995703277449261980049359967124868011
def doubleX : F := 8203579866205854582994652895839043217039276987933843750242885611138419881919
def doubleY : F := 25144341177599634947914765793481644996665986882320453064187704428277536630897
def doubleSlope : F := 36151207210235103587278439357809647099248587909617483350821400956956226147089
def outX : F := 8203579866205854582994652895839043217039276987933843750242885611138419881919
def outY : F := 25144341177599634947914765793481644996665986882320453064187704428277536630897

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((157793472124885664183113886235547161072845 : Nat) • base) + ((157793472124885664183113886235547161072845 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep136.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21950383374920738125391128671308417804121995703277449261980049359967124868011 : Int)) * (47614537241267525240545808764576219179491825129767443309115112478355520555444 : Int) =
        (1 : Int) + (39864209119219598899593007913229724496506525985446491276267468879937452797559 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36151207210235103587278439357809647099248587909617483350821400956956226147089 : Int) * ((2 : Int) * (21950383374920738125391128671308417804121995703277449261980049359967124868011 : Int)) =
        (3 : Int) * (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) + (-40964 : Int) * (-40964 : Int) + (-4189269600472570988677968530643799326236806655728890616068012195907183224661 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) =
        (36151207210235103587278439357809647099248587909617483350821400956956226147089 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) - (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) + (-24923962428251954399281770950511802641958812214174484110941384498773004170260 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25144341177599634947914765793481644996665986882320453064187704428277536630897 : Int) =
        (36151207210235103587278439357809647099248587909617483350821400956956226147089 : Int) * ((24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) - (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int)) - (21950383374920738125391128671308417804121995703277449261980049359967124868011 : Int) + (-11263387856058006939298575855089181623899326606061445896448112488869270176912 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (315586944249771328366227772471094322145690 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (315586944249771328366227772471094322145690 : Nat) = 157793472124885664183113886235547161072845 + 157793472124885664183113886235547161072845 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep137
