import ShielddSecurity.ConcretePointTraceStep026
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep027
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41785182126575712996733242626911863401428220456880171445506002596551360092913
def inputY : F := 15764918051038113141343348741325440748789022200505035532985270659576151598433
def doubleX : F := 50164002177227998388068244692330561515137937488035730124225134062052445127465
def doubleY : F := 30444564358102861213985435358462683215846645980116264891021397328065510099318
def doubleSlope : F := 14985078120512798769050245932418090161100616427087448842677073376315840436937
def outX : F := 50164002177227998388068244692330561515137937488035730124225134062052445127465
def outY : F := 30444564358102861213985435358462683215846645980116264891021397328065510099318

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((121559669 : Nat) • base) + ((121559669 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep026.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15764918051038113141343348741325440748789022200505035532985270659576151598433 : Int)) * (27577464770878885489030369100558143864619223487305127572257556001352269592551 : Int) =
        (1 : Int) + (16582405489230014131977884587775781589185556139676546129606724366318833640205 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (14985078120512798769050245932418090161100616427087448842677073376315840436937 : Int) * ((2 : Int) * (15764918051038113141343348741325440748789022200505035532985270659576151598433 : Int)) =
        (3 : Int) * (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) + (-40964 : Int) * (-40964 : Int) + (-90882954904838425905387590478656260687702085755892279254490988053236249358161 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) =
        (14985078120512798769050245932418090161100616427087448842677073376315840436937 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) - (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) + (-4282422397412212023652017174639167777640513567205180636752740753145788430542 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30444564358102861213985435358462683215846645980116264891021397328065510099318 : Int) =
        (14985078120512798769050245932418090161100616427087448842677073376315840436937 : Int) * ((41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) - (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int)) - (15764918051038113141343348741325440748789022200505035532985270659576151598433 : Int) + (2394491797789305041112266965109881863060314885556611408071539470295629050575 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (243119338 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (243119338 : Nat) = 121559669 + 121559669 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep027
