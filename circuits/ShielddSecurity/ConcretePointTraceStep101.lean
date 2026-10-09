import ShielddSecurity.ConcretePointTraceStep100
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep101
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20009907507953071182540414653694349699384315542128005004506761726232438594975
def inputY : F := 7699252430780067967829821748328884041794849636796367412975894730947255241395
def doubleX : F := 216336399648223157118731964782775655145726175811068750054785231901207849557
def doubleY : F := 38721984196570982431023641772955493920986040998650679425521324927636306039705
def doubleSlope : F := 41170887020970897305014998647555301251743371662961923792605475022009361198798
def outX : F := 216336399648223157118731964782775655145726175811068750054785231901207849557
def outY : F := 38721984196570982431023641772955493920986040998650679425521324927636306039705

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2296197229951004034710260548098 : Nat) • base) + ((2296197229951004034710260548098 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep100.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7699252430780067967829821748328884041794849636796367412975894730947255241395 : Int)) * (8907848608637192968547519080800272352548343856194894749940838080869641017862 : Int) =
        (1 : Int) + (2615910379068282722559908012927435109230119707265280925538817728923545590883 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41170887020970897305014998647555301251743371662961923792605475022009361198798 : Int) * ((2 : Int) * (7699252430780067967829821748328884041794849636796367412975894730947255241395 : Int)) =
        (3 : Int) * (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) + (-40964 : Int) * (-40964 : Int) + (-10817385799110609521670002093077085906416992872563756039833363305687771010127 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) =
        (41170887020970897305014998647555301251743371662961923792605475022009361198798 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) - (20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) + (-32325996894920151465932626615442039463019067278337410980626982454239953307705 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (38721984196570982431023641772955493920986040998650679425521324927636306039705 : Int) =
        (41170887020970897305014998647555301251743371662961923792605475022009361198798 : Int) * ((20009907507953071182540414653694349699384315542128005004506761726232438594975 : Int) - (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int)) - (7699252430780067967829821748328884041794849636796367412975894730947255241395 : Int) + (-15541246849030234560731488562591147107769482779582001471976143978524346577728 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4592394459902008069420521096196 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4592394459902008069420521096196 : Nat) = 2296197229951004034710260548098 + 2296197229951004034710260548098 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep101
