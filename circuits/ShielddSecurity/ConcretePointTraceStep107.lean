import ShielddSecurity.ConcretePointTraceStep106
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep107
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 47261836653076542206426345388814688732549739126226105585364437971863815195032
def inputY : F := 3476147939496040528038821988927695444095907425586585802128365454886406624817
def doubleX : F := 42271710486129246561742685685715805035885852736653498750212965864288825586926
def doubleY : F := 17549804767462777576208908463604202386825901511286530986129048997192971675558
def doubleSlope : F := 38185891595298337956499412199269973811547982236209393831110278674927047939250
def outX : F := 42271710486129246561742685685715805035885852736653498750212965864288825586926
def outY : F := 17549804767462777576208908463604202386825901511286530986129048997192971675558

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((146956622716864258221456675078298 : Nat) • base) + ((146956622716864258221456675078298 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep106.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3476147939496040528038821988927695444095907425586585802128365454886406624817 : Int)) * (14802727975544757997233256730078316807338373604904850141393012444089432476610 : Int) =
        (1 : Int) + (1962643788408418509262279065885832998534169445643325511399727352800855054403 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (38185891595298337956499412199269973811547982236209393831110278674927047939250 : Int) * ((2 : Int) * (3476147939496040528038821988927695444095907425586585802128365454886406624817 : Int)) =
        (3 : Int) * (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) + (-40964 : Int) * (-40964 : Int) + (-122732079386470339007026247830086946969762123591867604720933635351474904236332 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) =
        (38185891595298337956499412199269973811547982236209393831110278674927047939250 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) - (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) + (-27808486309380399876888545223669096526513611310797013255722437198667139826606 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (17549804767462777576208908463604202386825901511286530986129048997192971675558 : Int) =
        (38185891595298337956499412199269973811547982236209393831110278674927047939250 : Int) * ((47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) - (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int)) - (3476147939496040528038821988927695444095907425586585802128365454886406624817 : Int) + (-3634008514619065292121353768281098235889787929599768923207682743892338092125 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (293913245433728516442913350156596 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (293913245433728516442913350156596 : Nat) = 146956622716864258221456675078298 + 146956622716864258221456675078298 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep107
