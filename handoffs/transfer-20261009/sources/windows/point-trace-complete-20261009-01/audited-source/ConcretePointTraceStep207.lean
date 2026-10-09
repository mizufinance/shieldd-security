import ShielddSecurity.ConcretePointTraceStep206
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep207
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15554741127752288852224946698076802847750581678159406389777700152018884942105
def inputY : F := 34580254930278276658034561888195209895813823561524007829938324466136888855133
def doubleX : F := 12954120461571035702056171298567756350964949136324326159491759066112627428829
def doubleY : F := 16082073374785284076261377653680591689523014299702631643648308234993077310527
def doubleSlope : F := 9389690915385409888547702512884612739940472975781810964889488327287677862529
def outX : F := 12954120461571035702056171298567756350964949136324326159491759066112627428829
def outY : F := 16082073374785284076261377653680591689523014299702631643648308234993077310527

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((186289650994546429101631234843900009812668976845552529123476664 : Nat) • base) + ((186289650994546429101631234843900009812668976845552529123476664 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep206.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (34580254930278276658034561888195209895813823561524007829938324466136888855133 : Int)) * (14367916750342355545387922522140651121478755358215307130965861982170863069618 : Int) =
        (1 : Int) + (18950621969576323805730425077374625541595278189054952183964433969576771433299 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (9389690915385409888547702512884612739940472975781810964889488327287677862529 : Int) * ((2 : Int) * (34580254930278276658034561888195209895813823561524007829938324466136888855133 : Int)) =
        (3 : Int) * (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) + (-40964 : Int) * (-40964 : Int) + (-1458049536843469278478391457972477292081058634475187326188463887616983381529 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) =
        (9389690915385409888547702512884612739940472975781810964889488327287677862529 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) - (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) + (-1681411727982265312331376655354473854155928012506480790022064571366406948090 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (16082073374785284076261377653680591689523014299702631643648308234993077310527 : Int) =
        (9389690915385409888547702512884612739940472975781810964889488327287677862529 : Int) * ((15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) - (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int)) - (34580254930278276658034561888195209895813823561524007829938324466136888855133 : Int) + (-465693080587491106663841793367375234839832915257552486028076768800946979488 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (372579301989092858203262469687800019625337953691105058246953328 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (372579301989092858203262469687800019625337953691105058246953328 : Nat) = 186289650994546429101631234843900009812668976845552529123476664 + 186289650994546429101631234843900009812668976845552529123476664 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep207
