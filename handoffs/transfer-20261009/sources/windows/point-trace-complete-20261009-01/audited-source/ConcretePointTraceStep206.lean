import ShielddSecurity.ConcretePointTraceStep205
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep206
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28814607045722471110364957977252371237120881648332950145347460831244775941807
def inputY : F := 15814575136589955221349585958799725147342085565011021245672905698170615381466
def doubleX : F := 15554741127752288852224946698076802847750581678159406389777700152018884942105
def doubleY : F := 34580254930278276658034561888195209895813823561524007829938324466136888855133
def doubleSlope : F := 41549837378228367763188822236014131733174293972281235379602704276027554821673
def outX : F := 15554741127752288852224946698076802847750581678159406389777700152018884942105
def outY : F := 34580254930278276658034561888195209895813823561524007829938324466136888855133

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((93144825497273214550815617421950004906334488422776264561738332 : Nat) • base) + ((93144825497273214550815617421950004906334488422776264561738332 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep205.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15814575136589955221349585958799725147342085565011021245672905698170615381466 : Int)) * (31027897512110434471120039817099488735724583051394827493510465853509561789338 : Int) =
        (1 : Int) + (18715927402636400073846112728361332829432926014224972963122508652545224451655 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41549837378228367763188822236014131733174293972281235379602704276027554821673 : Int) * ((2 : Int) * (15814575136589955221349585958799725147342085565011021245672905698170615381466 : Int)) =
        (3 : Int) * (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) + (-40964 : Int) * (-40964 : Int) + (-22439955152959700402788420803194421315478102847133239446386499461804264460335 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int) =
        (41549837378228367763188822236014131733174293972281235379602704276027554821673 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) - (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) + (-32923813713252637246405510481445109659366972489789047340964075741115339369506 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34580254930278276658034561888195209895813823561524007829938324466136888855133 : Int) =
        (41549837378228367763188822236014131733174293972281235379602704276027554821673 : Int) * ((28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) - (15554741127752288852224946698076802847750581678159406389777700152018884942105 : Int)) - (15814575136589955221349585958799725147342085565011021245672905698170615381466 : Int) + (-10507029218234994387961759482192651716039001428053126617731002465234028480719 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (186289650994546429101631234843900009812668976845552529123476664 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (186289650994546429101631234843900009812668976845552529123476664 : Nat) = 93144825497273214550815617421950004906334488422776264561738332 + 93144825497273214550815617421950004906334488422776264561738332 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep206
