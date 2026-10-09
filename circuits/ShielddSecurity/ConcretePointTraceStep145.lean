import ShielddSecurity.ConcretePointTraceStep144
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep145
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 23205563505794635098949225240501162078543634659777595684979708311290565490253
def inputY : F := 47837759035518536943222766671967722103556233978764527288865151830917372821691
def doubleX : F := 3217164406942250688713204317082327471730732295092474899332778098584295944176
def doubleY : F := 1064446204116300190898886914470289042670945552971969977294460935733908085470
def doubleSlope : F := 38815937403006567275311949581844401297294898479125485381111694145832705072722
def outX : F := 3217164406942250688713204317082327471730732295092474899332778098584295944176
def outY : F := 1064446204116300190898886914470289042670945552971969977294460935733908085470

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((40395128863970730030877154876300073234648324 : Nat) • base) + ((40395128863970730030877154876300073234648324 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep144.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (47837759035518536943222766671967722103556233978764527288865151830917372821691 : Int)) * (16043134725601755422482639206060628245495524186237599074190046835635336796694 : Int) =
        (1 : Int) + (29272615765999737282155629524040900377636898940868813636908822747581362248739 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (38815937403006567275311949581844401297294898479125485381111694145832705072722 : Int) * ((2 : Int) * (47837759035518536943222766671967722103556233978764527288865151830917372821691 : Int)) =
        (3 : Int) * (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) + (-40964 : Int) * (-40964 : Int) + (40015359342691580254851924896038626293124634217787859101487374934193737889553 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) =
        (38815937403006567275311949581844401297294898479125485381111694145832705072722 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) - (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) + (-28733705529698890817201487702426032784778496405508883701027356801212155786690 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1064446204116300190898886914470289042670945552971969977294460935733908085470 : Int) =
        (38815937403006567275311949581844401297294898479125485381111694145832705072722 : Int) * ((23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) - (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int)) - (47837759035518536943222766671967722103556233978764527288865151830917372821691 : Int) + (-14796519474808209908708897058322642793643962666467706762368990807438297633841 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (80790257727941460061754309752600146469296648 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (80790257727941460061754309752600146469296648 : Nat) = 40395128863970730030877154876300073234648324 + 40395128863970730030877154876300073234648324 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep145
