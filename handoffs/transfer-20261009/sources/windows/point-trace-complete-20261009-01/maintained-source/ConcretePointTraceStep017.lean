import ShielddSecurity.ConcretePointTraceStep016
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep017
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31351039174741370791392834605725171092213821371365588115107764312007852760660
def inputY : F := 48978444531009348041142931747681118351514905800360769278864904733304207524679
def doubleX : F := 26324246366869107796277568976615373039317450687766183658241948382884909483185
def doubleY : F := 24000610487331934228857100878638718736633173313058701039188944328789428838620
def doubleSlope : F := 49989810836098246137473522055662664294030296693309655907484954836286333726231
def addX : F := 49572775152340724237764497713283390171381050695988256822223678367978494173491
def addY : F := 18389945054155396692988255310000093496342317570943788482869097001183762115676
def addSlope : F := 49371476867241123634191247185091686422951612645570432374882006683126382848343
def outX : F := 49572775152340724237764497713283390171381050695988256822223678367978494173491
def outY : F := 18389945054155396692988255310000093496342317570943788482869097001183762115676

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((118710 : Nat) • base) + ((118710 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep016.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (48978444531009348041142931747681118351514905800360769278864904733304207524679 : Int)) * (9203908902679762846500910044179802620998017829491794413386705934132930740954 : Int) =
        (1 : Int) + (17194073338255444352791638245677529944745939407563366479432231308567049777387 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49989810836098246137473522055662664294030296693309655907484954836286333726231 : Int) * ((2 : Int) * (48978444531009348041142931747681118351514905800360769278864904733304207524679 : Int)) =
        (3 : Int) * (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) + (-40964 : Int) * (-40964 : Int) + (37153635288586241570586531654323383097875227513738770752054348513818212375874 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int) =
        (49989810836098246137473522055662664294030296693309655907484954836286333726231 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) - (31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) + (-47657852168629731721393715896483676642762225004515429429806641783952676013248 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24000610487331934228857100878638718736633173313058701039188944328789428838620 : Int) =
        (49989810836098246137473522055662664294030296693309655907484954836286333726231 : Int) * ((31351039174741370791392834605725171092213821371365588115107764312007852760660 : Int) - (26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int)) - (48978444531009348041142931747681118351514905800360769278864904733304207524679 : Int) + (-4792299560911998055061724632602854394023578303253370398708133165510080508802 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((118710 : Nat) • base) + ((118710 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (21856868607395942805453666968569414861170838710235752080663715005988503067529 : Int) =
        (1 : Int) + (-5567172721224860410427768406631635966379813731528220975400593481346905373811 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (49371476867241123634191247185091686422951612645570432374882006683126382848343 : Int) * ((26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (24000610487331934228857100878638718736633173313058701039188944328789428838620 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-12575430824929873323314504349066551973611885711724385196790624040619082872576 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int) =
        (49371476867241123634191247185091686422951612645570432374882006683126382848343 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-46486164670878105242508211411152665000547523533257764265943259630865547144866 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (18389945054155396692988255310000093496342317570943788482869097001183762115676 : Int) =
        (49371476867241123634191247185091686422951612645570432374882006683126382848343 : Int) * ((26324246366869107796277568976615373039317450687766183658241948382884909483185 : Int) - (49572775152340724237764497713283390171381050695988256822223678367978494173491 : Int)) - (24000610487331934228857100878638718736633173313058701039188944328789428838620 : Int) + (21889864473431838626375574247668369968006136987314243116614701782245267443558 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (237421 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (237421 : Nat) = 118710 + 118710 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep017
