import ShielddSecurity.ConcretePointTraceStep177
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep178
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41675841784311437110671266299111971491936841048584217071604886606650932902661
def inputY : F := 13861758892827646495578889041375087890991535615956654582845615209234125345271
def doubleX : F := 19827393878700480415011597873652052399130743075703422288040034091050675784449
def doubleY : F := 14243963328953454570515078316239871483239472673724091757864261522202684908057
def doubleSlope : F := 20050438603083834882776156286925775545793284238145708258564767095604661714091
def outX : F := 19827393878700480415011597873652052399130743075703422288040034091050675784449
def outY : F := 14243963328953454570515078316239871483239472673724091757864261522202684908057

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((346991514776919836367724900774471480050438971902341636 : Nat) • base) + ((346991514776919836367724900774471480050438971902341636 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep177.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (13861758892827646495578889041375087890991535615956654582845615209234125345271 : Int)) * (15814499228902689681514292597087979102967969193373710658643091458653738899846 : Int) =
        (1 : Int) + (8361327987364149375725990290674590402141760364933438605646096633089971850387 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (20050438603083834882776156286925775545793284238145708258564767095604661714091 : Int) * ((2 : Int) * (13861758892827646495578889041375087890991535615956654582845615209234125345271 : Int)) =
        (3 : Int) * (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) + (-40964 : Int) * (-40964 : Int) + (-88770496506905897653845976017535753968028938691805955296975215115734232855057 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) =
        (20050438603083834882776156286925775545793284238145708258564767095604661714091 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) - (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) + (-7666890022019489549237629154647304171638261445040199768153798054831249463606 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (14243963328953454570515078316239871483239472673724091757864261522202684908057 : Int) =
        (20050438603083834882776156286925775545793284238145708258564767095604661714091 : Int) * ((41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) - (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int)) - (13861758892827646495578889041375087890991535615956654582845615209234125345271 : Int) + (-8354413115849626726533037868368931048418265251772300105089521054041003331228 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (693983029553839672735449801548942960100877943804683272 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (693983029553839672735449801548942960100877943804683272 : Nat) = 346991514776919836367724900774471480050438971902341636 + 346991514776919836367724900774471480050438971902341636 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep178
