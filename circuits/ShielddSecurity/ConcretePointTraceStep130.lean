import ShielddSecurity.ConcretePointTraceStep129
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep130
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44843405650800629261716256516217572724457902466549576949706066886690513495984
def inputY : F := 21711775159466432182898360686226105420227472204704398068697468228613577347923
def doubleX : F := 38555165338838361078291570424132320239233528502532900733760793004324426765606
def doubleY : F := 40136842237520599079550125363760319978981014092722730607736320433592882870906
def doubleSlope : F := 12482370455187059702141170545218226679133731367795173500473627850975829059671
def addX : F := 31064732792922849611614979585316239990262623870026372100056844447085781120353
def addY : F := 7890566641986631886466338004070462272929878721315277994735447770683241547753
def addSlope : F := 1774296864205746711998520904891758701186200535863220154059320224090012192143
def outX : F := 31064732792922849611614979585316239990262623870026372100056844447085781120353
def outY : F := 7890566641986631886466338004070462272929878721315277994735447770683241547753

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1232761500975669251430577236215212195881 : Nat) • base) + ((1232761500975669251430577236215212195881 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep129.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21711775159466432182898360686226105420227472204704398068697468228613577347923 : Int)) * (27015021239022424445738714084452259016060431108239659666145781875465907711807 : Int) =
        (1 : Int) + (22371861444513540300287213420040538288304731394157999953787295949143532109017 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (12482370455187059702141170545218226679133731367795173500473627850975829059671 : Int) * ((2 : Int) * (21711775159466432182898360686226105420227472204704398068697468228613577347923 : Int)) =
        (3 : Int) * (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) + (-40964 : Int) * (-40964 : Int) + (-104713885888015662721521000207582044524212107568072425616042561068315731967398 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int) =
        (12482370455187059702141170545218226679133731367795173500473627850975829059671 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) - (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) + (-2971430755377905976793381260466027499074840682146224071719137578680138066195 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (40136842237520599079550125363760319978981014092722730607736320433592882870906 : Int) =
        (12482370455187059702141170545218226679133731367795173500473627850975829059671 : Int) * ((44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) - (38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int)) - (21711775159466432182898360686226105420227472204704398068697468228613577347923 : Int) + (-1496916849828571191619122562891836311692140193056421586715815866615015296793 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1232761500975669251430577236215212195881 : Nat) • base) + ((1232761500975669251430577236215212195881 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (37324344858972851904712836997078248242369450892877124936155853306141355358637 : Int) =
        (1 : Int) + (-800818309891715400302073484751054810231262661779086789297316512599064273450 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (1774296864205746711998520904891758701186200535863220154059320224090012192143 : Int) * ((38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (40136842237520599079550125363760319978981014092722730607736320433592882870906 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-38068703453687860517410673173023931051188564625007264676962293848803769267 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) =
        (1774296864205746711998520904891758701186200535863220154059320224090012192143 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-60037700368615422877843670330632151651202084480504766138883081176423556175 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (7890566641986631886466338004070462272929878721315277994735447770683241547753 : Int) =
        (1774296864205746711998520904891758701186200535863220154059320224090012192143 : Int) * ((38555165338838361078291570424132320239233528502532900733760793004324426765606 : Int) - (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int)) - (40136842237520599079550125363760319978981014092722730607736320433592882870906 : Int) + (-253457216712328402256952002711604286549053970332536283204899852095843696040 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2465523001951338502861154472430424391763 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2465523001951338502861154472430424391763 : Nat) = 1232761500975669251430577236215212195881 + 1232761500975669251430577236215212195881 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep130
