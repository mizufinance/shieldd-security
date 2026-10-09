import ShielddSecurity.ConcretePointTraceStep241
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep242
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 5662833352520234119656012538123274397754530599769795687764545896965844772978
def inputY : F := 14539788680085699392283015300711804488774124497474672376552987941847752158441
def doubleX : F := 50913547063236267894845220072698185523678018183223156874149214014707768159028
def doubleY : F := 21401289352551848955399592228220798903483060655581350929226333492081455390711
def doubleSlope : F := 22374386493599192961096382726904260531580512551130843674980906323570896268308
def outX : F := 50913547063236267894845220072698185523678018183223156874149214014707768159028
def outY : F := 21401289352551848955399592228220798903483060655581350929226333492081455390711

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((6400863668838646298760710511253169657915938736203434845083358557023616459 : Nat) • base) + ((6400863668838646298760710511253169657915938736203434845083358557023616459 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep241.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (14539788680085699392283015300711804488774124497474672376552987941847752158441 : Int)) * (20680576296520155158002992054009789824988859336468411895919565525909523729010 : Int) =
        (1 : Int) + (11468911623179320929513347924797555425473945512607878269128837724188938482563 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22374386493599192961096382726904260531580512551130843674980906323570896268308 : Int) * ((2 : Int) * (14539788680085699392283015300711804488774124497474672376552987941847752158441 : Int)) =
        (3 : Int) * (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) + (-40964 : Int) * (-40964 : Int) + (10573574987354273185246247437737659629022910505841554697705835286396893113132 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int) =
        (22374386493599192961096382726904260531580512551130843674980906323570896268308 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) - (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) + (-9547150100823109402630234257532448884104677042144860313718020773456053364096 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21401289352551848955399592228220798903483060655581350929226333492081455390711 : Int) =
        (22374386493599192961096382726904260531580512551130843674980906323570896268308 : Int) * ((5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) - (50913547063236267894845220072698185523678018183223156874149214014707768159028 : Int)) - (14539788680085699392283015300711804488774124497474672376552987941847752158441 : Int) + (19308478294552124798492561917424145645060347252242505454839055957554329066504 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (12801727337677292597521421022506339315831877472406869690166717114047232918 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (12801727337677292597521421022506339315831877472406869690166717114047232918 : Nat) = 6400863668838646298760710511253169657915938736203434845083358557023616459 + 6400863668838646298760710511253169657915938736203434845083358557023616459 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep242
