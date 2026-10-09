import ShielddSecurity.ConcretePointTraceStep019
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep020
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 49056106695774809107938619486548960382363112656046507238744502358430440494009
def inputY : F := 8925631949118034708956953249085150013483980153936577528223624562751192356671
def doubleX : F := 4207251075505944282771509912383856120140841579252474204346983953561889514573
def doubleY : F := 15508284976220786873225712564295282615938929536744961189783131758551518330796
def doubleSlope : F := 5959796139384604495800251283670966528002983906699475737080530834873114990444
def addX : F := 26685049616425729967417054853767827740913623562056978350507063453246526208038
def addY : F := 39550046607826240993394033592819401558175799121462689217124476977557117580830
def addSlope : F := 11268128139307790085576445039015645843516629691132780360723785559982940619662
def outX : F := 26685049616425729967417054853767827740913623562056978350507063453246526208038
def outY : F := 39550046607826240993394033592819401558175799121462689217124476977557117580830

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((949684 : Nat) • base) + ((949684 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep019.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8925631949118034708956953249085150013483980153936577528223624562751192356671 : Int)) * (9068707450211308183112481469601296539862957671081330019735991134626466843151 : Int) =
        (1 : Int) + (3087349822405858387110221674089343976620770171103986096798582022482506261857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (5959796139384604495800251283670966528002983906699475737080530834873114990444 : Int) * ((2 : Int) * (8925631949118034708956953249085150013483980153936577528223624562751192356671 : Int)) =
        (3 : Int) * (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) + (-40964 : Int) * (-40964 : Int) + (-135653593937764668859545852021327664617217801028291153614039759631913454487659 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int) =
        (5959796139384604495800251283670966528002983906699475737080530834873114990444 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) - (49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) + (-677382992167025594320527658411335830374200745168078676002568123024886499801 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15508284976220786873225712564295282615938929536744961189783131758551518330796 : Int) =
        (5959796139384604495800251283670966528002983906699475737080530834873114990444 : Int) * ((49056106695774809107938619486548960382363112656046507238744502358430440494009 : Int) - (4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int)) - (8925631949118034708956953249085150013483980153936577528223624562751192356671 : Int) + (-5097464964374033653805096496626844208073737340068003806962229493954024185509 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((949684 : Nat) • base) + ((949684 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (33858810556434092879673653544000094744491546896492157974924676932350036852467 : Int) =
        (1 : Int) + (-22905543982893162904496412423130586764584241589185506082503120648809493255667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (11268128139307790085576445039015645843516629691132780360723785559982940619662 : Int) * ((4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (15508284976220786873225712564295282615938929536744961189783131758551518330796 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-7622908201975931003660064375029298214721370837995961617191609760743651528790 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) =
        (11268128139307790085576445039015645843516629691132780360723785559982940619662 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-2421447364801315647451693470493765354390148022659515269991448375304065359686 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (39550046607826240993394033592819401558175799121462689217124476977557117580830 : Int) =
        (11268128139307790085576445039015645843516629691132780360723785559982940619662 : Int) * ((4207251075505944282771509912383856120140841579252474204346983953561889514573 : Int) - (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int)) - (15508284976220786873225712564295282615938929536744961189783131758551518330796 : Int) + (4830332542418946697251606752004811731441296795081109657520071244498702435112 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1899369 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1899369 : Nat) = 949684 + 949684 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep020
