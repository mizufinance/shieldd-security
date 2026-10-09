import ShielddSecurity.ConcretePointTraceStep105
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep106
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 13796702754189404292833322356193779546928824053480762761012684000557665146781
def inputY : F := 16070313979432645508107480497018209570929959795736087263749848496893827904414
def doubleX : F := 47261836653076542206426345388814688732549739126226105585364437971863815195032
def doubleY : F := 3476147939496040528038821988927695444095907425586585802128365454886406624817
def doubleSlope : F := 25739996176987843876844678390174154045012268448237673833962614205903074128617
def outX : F := 47261836653076542206426345388814688732549739126226105585364437971863815195032
def outY : F := 3476147939496040528038821988927695444095907425586585802128365454886406624817

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((73478311358432129110728337539149 : Nat) • base) + ((73478311358432129110728337539149 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep105.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16070313979432645508107480497018209570929959795736087263749848496893827904414 : Int)) * (48717680939768192550198865383373672180203576807829178269686172022358241697220 : Int) =
        (1 : Int) + (29861556670395060513315141785362776652148939007277015369665022387757402805743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25739996176987843876844678390174154045012268448237673833962614205903074128617 : Int) * ((2 : Int) * (16070313979432645508107480497018209570929959795736087263749848496893827904414 : Int)) =
        (3 : Int) * (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) + (-40964 : Int) * (-40964 : Int) + (4886971358234644500818900426285710515881704562709513199949846925080355792001 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int) =
        (25739996176987843876844678390174154045012268448237673833962614205903074128617 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) - (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) + (-12635383713508398652814058084833942299739644331144098912005793123655035150151 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3476147939496040528038821988927695444095907425586585802128365454886406624817 : Int) =
        (25739996176987843876844678390174154045012268448237673833962614205903074128617 : Int) * ((13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) - (47261836653076542206426345388814688732549739126226105585364437971863815195032 : Int)) - (16070313979432645508107480497018209570929959795736087263749848496893827904414 : Int) + (16427539651867138480662463486965547421616476239121524821750622010782191668546 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (146956622716864258221456675078298 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (146956622716864258221456675078298 : Nat) = 73478311358432129110728337539149 + 73478311358432129110728337539149 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep106
