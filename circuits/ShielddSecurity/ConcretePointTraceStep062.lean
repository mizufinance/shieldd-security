import ShielddSecurity.ConcretePointTraceStep061
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep062
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 34042055887528668309919568744991815910690586088277638238387337863136485591305
def inputY : F := 2624940459950538670799802193709391672391317389753127116179467863670286874285
def doubleX : F := 9867187175390698469449111545990037690958776529031944726895092268896072123358
def doubleY : F := 11657355169897232660018591063280301913857762733400665118460616232932926488131
def doubleSlope : F := 30944744276439353875333580753500370923624166200847165683987429546066112040362
def outX : F := 9867187175390698469449111545990037690958776529031944726895092268896072123358
def outY : F := 11657355169897232660018591063280301913857762733400665118460616232932926488131

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4176758429732224676 : Nat) • base) + ((4176758429732224676 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep061.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2624940459950538670799802193709391672391317389753127116179467863670286874285 : Int)) * (50309625238471194031787868791496905615716320158021446074390110259883014231592 : Int) =
        (1 : Int) + (5037000731745448322405466943225418906113169489413252584970798936105523532303 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (30944744276439353875333580753500370923624166200847165683987429546066112040362 : Int) * ((2 : Int) * (2624940459950538670799802193709391672391317389753127116179467863670286874285 : Int)) =
        (3 : Int) * (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) + (-40964 : Int) * (-40964 : Int) + (-63203455144635203465587888897767208543418971828286895135048285199662024074927 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int) =
        (30944744276439353875333580753500370923624166200847165683987429546066112040362 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) - (34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) + (-18261871192882625068772579587562221695230571434172386649451702548370797928188 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (11657355169897232660018591063280301913857762733400665118460616232932926488131 : Int) =
        (30944744276439353875333580753500370923624166200847165683987429546066112040362 : Int) * ((34042055887528668309919568744991815910690586088277638238387337863136485591305 : Int) - (9867187175390698469449111545990037690958776529031944726895092268896072123358 : Int)) - (2624940459950538670799802193709391672391317389753127116179467863670286874285 : Int) + (-14266666241673994120464480749226921782043659484593711145656897950540428863646 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (8353516859464449352 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (8353516859464449352 : Nat) = 4176758429732224676 + 4176758429732224676 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep062
