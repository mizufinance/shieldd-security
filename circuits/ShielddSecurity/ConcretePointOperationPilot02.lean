import ShielddSecurity.ConcretePointOperationPilot01
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointOperationPilot02
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 21393289750074163033520183963327281622799057116362233550947986343578876885527
def inputY : F := 44648599647213915497370463328261413339747416338771684073573383575116587694472
def doubleX : F := 10286615931958241096886276449956395900684261632508179170169136407276153731696
def doubleY : F := 29843824260285434466895893477884032523725397456128018895678605836388581050494
def doubleSlope : F := 19077392125382583493535393488833437194656486409865304523344645210299295838247
def addX : F := 30820318921783750312400880173180348960265148459921400331265156797840279241074
def addY : F := 7276904971089403592571761354287873523245317394885197382647934966827059832099
def addSlope : F := 5103920133882618889642022121242476875254673092966661221499153925341564565128

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3 : Nat) • base) + ((3 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointOperationPilot01.prefix_three
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (44648599647213915497370463328261413339747416338771684073573383575116587694472 : Int)) * (3146047398022494605799547855909891617045295939024186556719451205966982286011 : Int) =
        (1 : Int) + (5357652953300874015631009648854743025463609671859305433731815766984273570991 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19077392125382583493535393488833437194656486409865304523344645210299295838247 : Int) * ((2 : Int) * (44648599647213915497370463328261413339747416338771684073573383575116587694472 : Int)) =
        (3 : Int) * (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) + (-40964 : Int) * (-40964 : Int) + (6303683242482592815219476888570460300115927528416259668709709175332775583389 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int) =
        (19077392125382583493535393488833437194656486409865304523344645210299295838247 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) - (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) + (-6940799387634775821706772196575340093410282952686798233622348707732158674779 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29843824260285434466895893477884032523725397456128018895678605836388581050494 : Int) =
        (19077392125382583493535393488833437194656486409865304523344645210299295838247 : Int) * ((21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) - (10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int)) - (44648599647213915497370463328261413339747416338771684073573383575116587694472 : Int) + (-4040866504645074471770592619786936404307897537620907463440901497991298252907 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3 : Nat) • base) + ((3 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (25678926099385848065473246920257874548270441707515624159887202516040457165434 : Int) =
        (1 : Int) + (-14394648025106622915518542376407995257977728569516550178117836563587385447343 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (5103920133882618889642022121242476875254673092966661221499153925341564565128 : Int) * ((10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29843824260285434466895893477884032523725397456128018895678605836388581050494 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2861067226532206905601376671702228027499587225700192852758969637679134873068 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int) =
        (5103920133882618889642022121242476875254673092966661221499153925341564565128 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-496797290901508811189053636865026073735094687405169681241773392498229904723 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (7276904971089403592571761354287873523245317394885197382647934966827059832099 : Int) =
        (5103920133882618889642022121242476875254673092966661221499153925341564565128 : Int) * ((10286615931958241096886276449956395900684261632508179170169136407276153731696 : Int) - (30820318921783750312400880173180348960265148459921400331265156797840279241074 : Int)) - (29843824260285434466895893477884032523725397456128018895678605836388581050494 : Int) + (1998677046257270383404685567228578472201062934498636133070909300187479511729 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_seven : ∃ output : curve.Equation addX addY,
    (7 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [show (7 : Nat) = 3 + 3 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointOperationPilot02
