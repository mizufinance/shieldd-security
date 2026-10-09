import ShielddSecurity.ConcretePointTraceStep022
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep023
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 38439087630322202178229879914649168004902204394713509398658890635378057245065
def inputY : F := 46275397629657095332362339719628345255508459648397163276710854745663506398147
def doubleX : F := 33398432023260150952169772432154959594783542313806192053911600062056019166216
def doubleY : F := 36209090643843098286923363715419460461412935510456569776365276736634679399790
def doubleSlope : F := 16268126159153601230167585959729415587508086240014171917642478897449016012516
def outX : F := 33398432023260150952169772432154959594783542313806192053911600062056019166216
def outY : F := 36209090643843098286923363715419460461412935510456569776365276736634679399790

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((7597479 : Nat) • base) + ((7597479 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep022.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (46275397629657095332362339719628345255508459648397163276710854745663506398147 : Int)) * (38645628237368740270573811398874469455866618204034193863647124360680467326810 : Int) =
        (1 : Int) + (68210621348815465790150063983683269523443674628596906247727577252702312722203 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16268126159153601230167585959729415587508086240014171917642478897449016012516 : Int) * ((2 : Int) * (46275397629657095332362339719628345255508459648397163276710854745663506398147 : Int)) =
        (3 : Int) * (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) + (-40964 : Int) * (-40964 : Int) + (-55821750859891231599329945627491822568517679302200758685879025320647117476379 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) =
        (16268126159153601230167585959729415587508086240014171917642478897449016012516 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) - (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) + (-5047153839737562822116630687793361765019662097371786916558569215577760273406 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36209090643843098286923363715419460461412935510456569776365276736634679399790 : Int) =
        (16268126159153601230167585959729415587508086240014171917642478897449016012516 : Int) * ((38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) - (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int)) - (46275397629657095332362339719628345255508459648397163276710854745663506398147 : Int) + (-1563853393629051566210161988125697024566469007634259278083869674101827920819 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (15194958 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (15194958 : Nat) = 7597479 + 7597479 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep023
