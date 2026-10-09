import ShielddSecurity.ConcretePointTraceStep186
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep187
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20522956576139066457096458101918878226645455583682215137754180798539380984290
def inputY : F := 34340343647199510772018322333983488868541239391279071219131531861272583706286
def doubleX : F := 18695813035194046396366673229820625953850712034663954715333015194480505519419
def doubleY : F := 47154185914286160450092003886160297445134984455528562844169721522307633965972
def doubleSlope : F := 24254014691247785280509943980911337297403947227755762880353234115845946815679
def outX : F := 18695813035194046396366673229820625953850712034663954715333015194480505519419
def outY : F := 47154185914286160450092003886160297445134984455528562844169721522307633965972

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((177659655565782956220275149196529397785824753613998917697 : Nat) • base) + ((177659655565782956220275149196529397785824753613998917697 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep186.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (34340343647199510772018322333983488868541239391279071219131531861272583706286 : Int)) * (13321536743434662007396797928742307788917814355145847445316924411895508362720 : Int) =
        (1 : Int) + (17448594045602879795218453124611038081819775571459839494305395649316610047103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24254014691247785280509943980911337297403947227755762880353234115845946815679 : Int) * ((2 : Int) * (34340343647199510772018322333983488868541239391279071219131531861272583706286 : Int)) =
        (3 : Int) * (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) + (-40964 : Int) * (-40964 : Int) + (7670457628899712070021792638765274068542405277388572280585441425421968941864 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) =
        (24254014691247785280509943980911337297403947227755762880353234115845946815679 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) - (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) + (-11218602277135497821857030351581504078604761014085289475990057977845541426570 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (47154185914286160450092003886160297445134984455528562844169721522307633965972 : Int) =
        (24254014691247785280509943980911337297403947227755762880353234115845946815679 : Int) * ((20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) - (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int)) - (34340343647199510772018322333983488868541239391279071219131531861272583706286 : Int) + (-845138297722564281469831516619925701985823945200667139423890912352034839127 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (355319311131565912440550298393058795571649507227997835394 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (355319311131565912440550298393058795571649507227997835394 : Nat) = 177659655565782956220275149196529397785824753613998917697 + 177659655565782956220275149196529397785824753613998917697 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep187
