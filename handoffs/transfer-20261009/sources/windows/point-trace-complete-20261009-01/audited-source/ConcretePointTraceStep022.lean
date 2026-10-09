import ShielddSecurity.ConcretePointTraceStep021
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep022
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48729963439747569481026778906047914116475299456273893559552974666925363753639
def inputY : F := 37742825584509623287984469049684445162014008606354774621860369387940812796195
def doubleX : F := 18627257390590455160449017718037100399480625551197489235552809839502955090615
def doubleY : F := 33747485939188599703984907644062614228850008733812669255516826011941803471605
def doubleSlope : F := 49204440189098186128986159512016229367906690680700765772953360524492040975460
def addX : F := 38439087630322202178229879914649168004902204394713509398658890635378057245065
def addY : F := 46275397629657095332362339719628345255508459648397163276710854745663506398147
def addSlope : F := 38506184472147339051314064753713406623973499119183339769978142036450524988384
def outX : F := 38439087630322202178229879914649168004902204394713509398658890635378057245065
def outY : F := 46275397629657095332362339719628345255508459648397163276710854745663506398147

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3798739 : Nat) • base) + ((3798739 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep021.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37742825584509623287984469049684445162014008606354774621860369387940812796195 : Int)) * (27623540564840988800177770157644607514012202097037570310111983498669739065392 : Int) =
        (1 : Int) + (39766303893407299006544971651411525499863597827949488900805656979373764177183 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49204440189098186128986159512016229367906690680700765772953360524492040975460 : Int) * ((2 : Int) * (37742825584509623287984469049684445162014008606354774621860369387940812796195 : Int)) =
        (3 : Int) * (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) + (-40964 : Int) * (-40964 : Int) + (-65024161245499070649073236927527439736491338179830625566215722633126894974235 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int) =
        (49204440189098186128986159512016229367906690680700765772953360524492040975460 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) - (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) + (-46172146955430581451752229156630082757896665430530480670777212914766271680275 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33747485939188599703984907644062614228850008733812669255516826011941803471605 : Int) =
        (49204440189098186128986159512016229367906690680700765772953360524492040975460 : Int) * ((48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) - (18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int)) - (37742825584509623287984469049684445162014008606354774621860369387940812796195 : Int) + (-28247584204113378135024544639191422917609609327552344040953261834772041389480 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3798739 : Nat) • base) + ((3798739 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (24202837627183159321728437603983726156582945498632043213606307674187368288458 : Int) =
        (1 : Int) + (-9717416309081195916141356084774783191256417068683784069383899291963384615065 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (38506184472147339051314064753713406623973499119183339769978142036450524988384 : Int) * ((18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (33747485939188599703984907644062614228850008733812669255516826011941803471605 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-15460196475882508492490863673362203649783282140007554044337863840709044718667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int) =
        (38506184472147339051314064753713406623973499119183339769978142036450524988384 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-28276942792525300254900805393693326049236309545062651672978538399217747286197 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (46275397629657095332362339719628345255508459648397163276710854745663506398147 : Int) =
        (38506184472147339051314064753713406623973499119183339769978142036450524988384 : Int) * ((18627257390590455160449017718037100399480625551197489235552809839502955090615 : Int) - (38439087630322202178229879914649168004902204394713509398658890635378057245065 : Int)) - (33747485939188599703984907644062614228850008733812669255516826011941803471605 : Int) + (14548779578754151560957533630565319903825180562898276515206020539086932368504 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (7597479 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (7597479 : Nat) = 3798739 + 3798739 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
#check @addX
#print axioms addX

set_option pp.all true in
#check @addY
#print axioms addY

set_option pp.all true in
#check @addSlope
#print axioms addSlope

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
#check @next_add
#print axioms next_add

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep022
