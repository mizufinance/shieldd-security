import ShielddSecurity.ConcretePointTraceStep121
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep122
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20188749895620436335543643812449181685703889475670128215066296607655365558242
def inputY : F := 3933234886865394274785793801926709301810146412220650638850335657117869506191
def doubleX : F := 20368257134819937805971843041817577931024057560191165555032222071749816904024
def doubleY : F := 39833293445309375907166576289695680300022067106281976593773143118549020884056
def doubleSlope : F := 40970496651258115672324585101628263106791667771867716195083063962927478769177
def outX : F := 20368257134819937805971843041817577931024057560191165555032222071749816904024
def outY : F := 39833293445309375907166576289695680300022067106281976593773143118549020884056

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4815474613186208013400692328965672640 : Nat) • base) + ((4815474613186208013400692328965672640 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep121.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3933234886865394274785793801926709301810146412220650638850335657117869506191 : Int)) * (24089873591006369654760080218729810501578470508954068986343324532689700682855 : Int) =
        (1 : Int) + (3613981111667239857628116470828290254698004863161551053397416037843366469393 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40970496651258115672324585101628263106791667771867716195083063962927478769177 : Int) * ((2 : Int) * (3933234886865394274785793801926709301810146412220650638850335657117869506191 : Int)) =
        (3 : Int) * (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) + (-40964 : Int) * (-40964 : Int) + (-17172664526233208830013207946721182326787256247560493555785242316045811884174 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) =
        (40970496651258115672324585101628263106791667771867716195083063962927478769177 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) - (20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) + (-32012083144309088005186620439928569815590100018252283696480881768507089225053 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (39833293445309375907166576289695680300022067106281976593773143118549020884056 : Int) =
        (40970496651258115672324585101628263106791667771867716195083063962927478769177 : Int) * ((20188749895620436335543643812449181685703889475670128215066296607655365558242 : Int) - (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int)) - (3933234886865394274785793801926709301810146412220650638850335657117869506191 : Int) + (140257041919050327806711098782862439480140551555866897663428377573553900397 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (9630949226372416026801384657931345280 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (9630949226372416026801384657931345280 : Nat) = 4815474613186208013400692328965672640 + 4815474613186208013400692328965672640 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep122
