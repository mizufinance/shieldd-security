import ShielddSecurity.ConcretePointTraceStep208
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep209
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26916134465130630209421683523654143369306760625496507311075300474033539114514
def inputY : F := 48301988362936266024813782975498295120488919279325022034506959737919768484464
def doubleX : F := 49676393447017999906440435050155801703416048499904689375374582295913010105028
def doubleY : F := 34718489595183549454325811730205453388785037692216176134891498843089781754481
def doubleSlope : F := 39897818810910677857508287057923805735021530701895202776332083977285054407127
def addX : F := 5297138915587488379374633279901208516649367688275121498535529267565425959863
def addY : F := 24420121113789299165590744541647686372899212871229776009218402174320154019694
def addSlope : F := 43470221129766940211505559087645746988846533060446775703208801965243342557373
def outX : F := 5297138915587488379374633279901208516649367688275121498535529267565425959863
def outY : F := 24420121113789299165590744541647686372899212871229776009218402174320154019694

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((745158603978185716406524939375600039250675907382210116493906657 : Nat) • base) + ((745158603978185716406524939375600039250675907382210116493906657 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep208.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (48301988362936266024813782975498295120488919279325022034506959737919768484464 : Int)) * (3125939821781256844734311141111803782665100120739133974346456238674680950566 : Int) =
        (1 : Int) + (5759000241366867506432800226955293896271645469381070344736435819300363827519 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (39897818810910677857508287057923805735021530701895202776332083977285054407127 : Int) * ((2 : Int) * (48301988362936266024813782975498295120488919279325022034506959737919768484464 : Int)) =
        (3 : Int) * (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) + (-40964 : Int) * (-40964 : Int) + (32055402347602191393487319204804030499159834018779668198684325907132001361252 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int) =
        (39897818810910677857508287057923805735021530701895202776332083977285054407127 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) - (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) + (-30357764422770065371749517871092089545417042595595702403191836897507278785457 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34718489595183549454325811730205453388785037692216176134891498843089781754481 : Int) =
        (39897818810910677857508287057923805735021530701895202776332083977285054407127 : Int) * ((26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) - (49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int)) - (48301988362936266024813782975498295120488919279325022034506959737919768484464 : Int) + (17318003865023870933690247057699850825859636076075105783603551394529594648671 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((745158603978185716406524939375600039250675907382210116493906657 : Nat) • base) + ((745158603978185716406524939375600039250675907382210116493906657 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (30613551787132337305739637086373721918938733503162558882288540892412822613209 : Int) =
        (1 : Int) + (5836054691547066112711317349781310907119594731736684798133965348522509036808 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (43470221129766940211505559087645746988846533060446775703208801965243342557373 : Int) * ((49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34718489595183549454325811730205453388785037692216176134891498843089781754481 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (8287002753911067327835212249120845650848852879818412303383061223830405032550 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (5297138915587488379374633279901208516649367688275121498535529267565425959863 : Int) =
        (43470221129766940211505559087645746988846533060446775703208801965243342557373 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-36037543356713671193932220477778587088603264265978801688327002579846005216771 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (24420121113789299165590744541647686372899212871229776009218402174320154019694 : Int) =
        (43470221129766940211505559087645746988846533060446775703208801965243342557373 : Int) * ((49676393447017999906440435050155801703416048499904689375374582295913010105028 : Int) - (5297138915587488379374633279901208516649367688275121498535529267565425959863 : Int)) - (34718489595183549454325811730205453388785037692216176134891498843089781754481 : Int) + (-36791147313025717208639401037169880244014858416918301686861784743577163682490 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1490317207956371432813049878751200078501351814764420232987813315 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1490317207956371432813049878751200078501351814764420232987813315 : Nat) = 745158603978185716406524939375600039250675907382210116493906657 + 745158603978185716406524939375600039250675907382210116493906657 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep209
