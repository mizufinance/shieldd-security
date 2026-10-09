import ShielddSecurity.ConcretePointTraceStep178
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep179
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 19827393878700480415011597873652052399130743075703422288040034091050675784449
def inputY : F := 14243963328953454570515078316239871483239472673724091757864261522202684908057
def doubleX : F := 24931452984497419997275362289213400635533747478699840205571758617794644805676
def doubleY : F := 49201152357153201905421578983094378007312177511861083693393688811743793787408
def doubleSlope : F := 41499619620090467084206576762634399190345863775731955419470669737235777655331
def outX : F := 24931452984497419997275362289213400635533747478699840205571758617794644805676
def outY : F := 49201152357153201905421578983094378007312177511861083693393688811743793787408

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((693983029553839672735449801548942960100877943804683272 : Nat) • base) + ((693983029553839672735449801548942960100877943804683272 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep178.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (14243963328953454570515078316239871483239472673724091757864261522202684908057 : Int)) * (30686700418505667015691934201983624769461276905656669122812305067736893035720 : Int) =
        (1 : Int) + (16671800899210353916835602549594266118090014271360944075512318922628055117583 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41499619620090467084206576762634399190345863775731955419470669737235777655331 : Int) * ((2 : Int) * (14243963328953454570515078316239871483239472673724091757864261522202684908057 : Int)) =
        (3 : Int) * (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) + (-40964 : Int) * (-40964 : Int) + (54570959199730470407803145626976646209425182971245978226523671982748583123 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) =
        (41499619620090467084206576762634399190345863775731955419470669737235777655331 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) - (19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) + (-32844277374227176870161713124301663907200904696295031155773812756566333788835 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (49201152357153201905421578983094378007312177511861083693393688811743793787408 : Int) =
        (41499619620090467084206576762634399190345863775731955419470669737235777655331 : Int) * ((19827393878700480415011597873652052399130743075703422288040034091050675784449 : Int) - (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int)) - (14243963328953454570515078316239871483239472673724091757864261522202684908057 : Int) + (4039534206334953733529335388596065138234317293097073816794316236073395353354 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1387966059107679345470899603097885920201755887609366544 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1387966059107679345470899603097885920201755887609366544 : Nat) = 693983029553839672735449801548942960100877943804683272 + 693983029553839672735449801548942960100877943804683272 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep179
