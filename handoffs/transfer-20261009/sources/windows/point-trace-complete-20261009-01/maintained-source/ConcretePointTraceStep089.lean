import ShielddSecurity.ConcretePointTraceStep088
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep089
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28175284432758235473716657307710878332406389077251843513031922229973835423918
def inputY : F := 49877747558402224044475565124054595491095005357749711091665460176613971249038
def doubleX : F := 32669888196170295129130102360412865853502054249683973932511754814273944284330
def doubleY : F := 2233563748692398574704302608170879641645972072331674571535663269072270535137
def doubleSlope : F := 47073274464585666064351215394938594138762228816376772493605860566460377961579
def outX : F := 32669888196170295129130102360412865853502054249683973932511754814273944284330
def outY : F := 2233563748692398574704302608170879641645972072331674571535663269072270535137

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((560595026843506844411684704 : Nat) • base) + ((560595026843506844411684704 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep088.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (49877747558402224044475565124054595491095005357749711091665460176613971249038 : Int)) * (12250968901314532105539137433477079395686704624592657559703941384470282030591 : Int) =
        (1 : Int) + (23306590465585070539051082142941681639729749704536323105842270252119168841955 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (47073274464585666064351215394938594138762228816376772493605860566460377961579 : Int) * ((2 : Int) * (49877747558402224044475565124054595491095005357749711091665460176613971249038 : Int)) =
        (3 : Int) * (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) + (-40964 : Int) * (-40964 : Int) + (44135390792167049529957738390689804476071587692588377191225680009623272106168 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) =
        (47073274464585666064351215394938594138762228816376772493605860566460377961579 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) - (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) + (-42259105267482173369189270705166982208269096670715500920676752040070611367611 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2233563748692398574704302608170879641645972072331674571535663269072270535137 : Int) =
        (47073274464585666064351215394938594138762228816376772493605860566460377961579 : Int) * ((28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) - (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int)) - (49877747558402224044475565124054595491095005357749711091665460176613971249038 : Int) + (4034942028869195295443778621147399350464316903065088821074773090734306911171 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1121190053687013688823369408 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1121190053687013688823369408 : Nat) = 560595026843506844411684704 + 560595026843506844411684704 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep089
