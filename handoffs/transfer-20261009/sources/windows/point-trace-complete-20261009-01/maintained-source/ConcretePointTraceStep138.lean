import ShielddSecurity.ConcretePointTraceStep137
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep138
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 8203579866205854582994652895839043217039276987933843750242885611138419881919
def inputY : F := 25144341177599634947914765793481644996665986882320453064187704428277536630897
def doubleX : F := 28600812540328639534512694589287673135493447918800949312421894565277507935127
def doubleY : F := 9301666588035252764640567297508409597996991796281409084211844924194056565070
def doubleSlope : F := 26571949286940318113695504306623632874363942128802134794478268737959137509535
def outX : F := 28600812540328639534512694589287673135493447918800949312421894565277507935127
def outY : F := 9301666588035252764640567297508409597996991796281409084211844924194056565070

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((315586944249771328366227772471094322145690 : Nat) • base) + ((315586944249771328366227772471094322145690 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep137.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (25144341177599634947914765793481644996665986882320453064187704428277536630897 : Int)) * (15182035582201074641767346274734688639293802197886757497514959984775180693595 : Int) =
        (1 : Int) + (14560347516824015321002129192657385765256349492518085631073925250466465128533 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (26571949286940318113695504306623632874363942128802134794478268737959137509535 : Int) * ((2 : Int) * (25144341177599634947914765793481644996665986882320453064187704428277536630897 : Int)) =
        (3 : Int) * (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) + (-40964 : Int) * (-40964 : Int) + (21633512277561051555383684573764613527453995565402319485179212881551796131515 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28600812540328639534512694589287673135493447918800949312421894565277507935127 : Int) =
        (26571949286940318113695504306623632874363942128802134794478268737959137509535 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) - (8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) + (-13465370541629924815914788087945047139905062727710261814774836059127331346356 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (9301666588035252764640567297508409597996991796281409084211844924194056565070 : Int) =
        (26571949286940318113695504306623632874363942128802134794478268737959137509535 : Int) * ((8203579866205854582994652895839043217039276987933843750242885611138419881919 : Int) - (28600812540328639534512694589287673135493447918800949312421894565277507935127 : Int)) - (25144341177599634947914765793481644996665986882320453064187704428277536630897 : Int) + (10336324709000307971894254572899281503592569957816917974271499920438594444519 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (631173888499542656732455544942188644291380 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (631173888499542656732455544942188644291380 : Nat) = 315586944249771328366227772471094322145690 + 315586944249771328366227772471094322145690 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep138
