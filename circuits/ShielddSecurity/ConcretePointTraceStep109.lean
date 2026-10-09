import ShielddSecurity.ConcretePointTraceStep108
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep109
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3906492616966488503419140274161744708001055681220852834327692936250800258413
def inputY : F := 41299294879376208240297677359490472671110798201429475902660053619498971086947
def doubleX : F := 29029775996875346494901481645759474129371539048410124523547708471579330733989
def doubleY : F := 6438861877568413578239490431177503265792099384497642227331954877855547034965
def doubleSlope : F := 10448830827301721204538385596187294932017984999610385407709894357413817035257
def outX : F := 29029775996875346494901481645759474129371539048410124523547708471579330733989
def outY : F := 6438861877568413578239490431177503265792099384497642227331954877855547034965

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((587826490867457032885826700313192 : Nat) • base) + ((587826490867457032885826700313192 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep108.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (41299294879376208240297677359490472671110798201429475902660053619498971086947 : Int)) * (16590932991132653415705024900812156099811348451904271524958968589447653741797 : Int) =
        (1 : Int) + (26134543635872846896966843439059167618135685417237025074417790840245223041309 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10448830827301721204538385596187294932017984999610385407709894357413817035257 : Int) * ((2 : Int) * (41299294879376208240297677359490472671110798201429475902660053619498971086947 : Int)) =
        (3 : Int) * (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) + (-40964 : Int) * (-40964 : Int) + (15586211435092970302492242483750270776226007573751987316987293460925852806171 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) =
        (10448830827301721204538385596187294932017984999610385407709894357413817035257 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) - (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) + (-2082125363464156716584938819532842958607397046211962154153805265095498535354 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (6438861877568413578239490431177503265792099384497642227331954877855547034965 : Int) =
        (10448830827301721204538385596187294932017984999610385407709894357413817035257 : Int) * ((3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) - (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int)) - (41299294879376208240297677359490472671110798201429475902660053619498971086947 : Int) + (5006285047904645936800923320629110469525091285902114849914395340481507120688 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1175652981734914065771653400626384 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1175652981734914065771653400626384 : Nat) = 587826490867457032885826700313192 + 587826490867457032885826700313192 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep109
