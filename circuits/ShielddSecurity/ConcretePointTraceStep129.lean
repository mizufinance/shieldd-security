import ShielddSecurity.ConcretePointTraceStep128
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep129
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45596172519381491962768255056820623148708810998180324175650622631853874496372
def inputY : F := 23453403055099768675533178844813844421104081826927027766201656293308587462910
def doubleX : F := 22037550167956348554828079219610019076025607287279325847891062482292537602370
def doubleY : F := 20509771603701857380882197869037816473613646805411633686687063306934583351999
def doubleSlope : F := 13735240007460349002817756505134763754571404212254504057706212137682302254195
def addX : F := 44843405650800629261716256516217572724457902466549576949706066886690513495984
def addY : F := 21711775159466432182898360686226105420227472204704398068697468228613577347923
def addSlope : F := 2440252656741789603995730293640522079777228262938676674878476678987280127767
def outX : F := 44843405650800629261716256516217572724457902466549576949706066886690513495984
def outY : F := 21711775159466432182898360686226105420227472204704398068697468228613577347923

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((616380750487834625715288618107606097940 : Nat) • base) + ((616380750487834625715288618107606097940 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep128.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (23453403055099768675533178844813844421104081826927027766201656293308587462910 : Int)) * (22350789756491498138590325592772960495178937212835880364158853941122943853945 : Int) =
        (1 : Int) + (19994024282346834672093457506784085358828533420188600357604907334050940189723 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13735240007460349002817756505134763754571404212254504057706212137682302254195 : Int) * ((2 : Int) * (23453403055099768675533178844813844421104081826927027766201656293308587462910 : Int)) =
        (3 : Int) * (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) + (-40964 : Int) * (-40964 : Int) + (-106658973206146020459086489970522795917564988950371319315809181548775281179212 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int) =
        (13735240007460349002817756505134763754571404212254504057706212137682302254195 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) - (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) + (-3597857715399242456536169527932690371186778592623569990621985364487736238983 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20509771603701857380882197869037816473613646805411633686687063306934583351999 : Int) =
        (13735240007460349002817756505134763754571404212254504057706212137682302254195 : Int) * ((45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) - (22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int)) - (23453403055099768675533178844813844421104081826927027766201656293308587462910 : Int) + (-6171029493857694658744195346003968041990318854941285375844116877612961380537 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((616380750487834625715288618107606097940 : Nat) • base) + ((616380750487834625715288618107606097940 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (28594499570768382586225979186391216171145723705783208968654537911065901739306 : Int) =
        (1 : Int) + (-9620952614889449125000620604659389155822771666719062223875208522930646782283 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (2440252656741789603995730293640522079777228262938676674878476678987280127767 : Int) * ((22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (20509771603701857380882197869037816473613646805411633686687063306934583351999 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-821051444553745843768560394322351183966754993358523464466551243444465478748 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int) =
        (2440252656741789603995730293640522079777228262938676674878476678987280127767 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-113564101082461464435243736942196686362722874928163115823425593912522449940 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21711775159466432182898360686226105420227472204704398068697468228613577347923 : Int) =
        (2440252656741789603995730293640522079777228262938676674878476678987280127767 : Int) * ((22037550167956348554828079219610019076025607287279325847891062482292537602370 : Int) - (44843405650800629261716256516217572724457902466549576949706066886690513495984 : Int)) - (20509771603701857380882197869037816473613646805411633686687063306934583351999 : Int) + (1061335378601242818228899821029566507229213410756502319136485010010107999220 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1232761500975669251430577236215212195881 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1232761500975669251430577236215212195881 : Nat) = 616380750487834625715288618107606097940 + 616380750487834625715288618107606097940 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep129
