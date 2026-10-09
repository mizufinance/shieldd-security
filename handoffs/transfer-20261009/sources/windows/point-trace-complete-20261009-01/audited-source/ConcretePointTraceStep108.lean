import ShielddSecurity.ConcretePointTraceStep107
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep108
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 42271710486129246561742685685715805035885852736653498750212965864288825586926
def inputY : F := 17549804767462777576208908463604202386825901511286530986129048997192971675558
def doubleX : F := 3906492616966488503419140274161744708001055681220852834327692936250800258413
def doubleY : F := 41299294879376208240297677359490472671110798201429475902660053619498971086947
def doubleSlope : F := 45073633362556659895739763210670772676632767640111179147731763042617798714926
def outX : F := 3906492616966488503419140274161744708001055681220852834327692936250800258413
def outY : F := 41299294879376208240297677359490472671110798201429475902660053619498971086947

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((293913245433728516442913350156596 : Nat) • base) + ((293913245433728516442913350156596 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep107.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (17549804767462777576208908463604202386825901511286530986129048997192971675558 : Int)) * (13081073980624862374256008155729443826283860207002189128183425191453249031823 : Int) =
        (1 : Int) + (8756230109328046572747018067110653316753224641953614250354857209745373721459 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (45073633362556659895739763210670772676632767640111179147731763042617798714926 : Int) * ((2 : Int) * (17549804767462777576208908463604202386825901511286530986129048997192971675558 : Int)) =
        (3 : Int) * (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) + (-40964 : Int) * (-40964 : Int) + (-72061838928087692361682919285295899552079954701360911938459849999873204015444 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int) =
        (45073633362556659895739763210670772676632767640111179147731763042617798714926 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) - (42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) + (-38745084690908690079410451209826053153026378486069716322463534082382397262083 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (41299294879376208240297677359490472671110798201429475902660053619498971086947 : Int) =
        (45073633362556659895739763210670772676632767640111179147731763042617798714926 : Int) * ((42271710486129246561742685685715805035885852736653498750212965864288825586926 : Int) - (3906492616966488503419140274161744708001055681220852834327692936250800258413 : Int)) - (17549804767462777576208908463604202386825901511286530986129048997192971675558 : Int) + (-32978562069076552611304329207054900605541707137049777205733009578517285877541 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (587826490867457032885826700313192 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (587826490867457032885826700313192 : Nat) = 293913245433728516442913350156596 + 293913245433728516442913350156596 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


set_option pp.all true in
#check @baseX
#print axioms baseX

set_option pp.all true in
#check @baseY
#print axioms baseY

set_option pp.all true in
#check @inputX
#print axioms inputX

set_option pp.all true in
#check @inputY
#print axioms inputY

set_option pp.all true in
#check @doubleX
#print axioms doubleX

set_option pp.all true in
#check @doubleY
#print axioms doubleY

set_option pp.all true in
#check @doubleSlope
#print axioms doubleSlope

set_option pp.all true in
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep108
