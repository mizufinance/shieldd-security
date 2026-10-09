import ShielddSecurity.ConcretePointTraceStep243
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep244
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 37358642005473444203882245883233558319416201610318860048502099871968502082644
def inputY : F := 12885287475909511778264964871177193019118005193927893854938256900211065153502
def doubleX : F := 24839792825461396775626266320921639093208782415654540471784566096822018176584
def doubleY : F := 27191964069339054588275470758277425230860864720520810368792178922275143880032
def doubleSlope : F := 13663030713446832055873942527930062764211151458337472355627542775893161108166
def addX : F := 33652555203852847325435703373215766219990032473577316466385438734209534304630
def addY : F := 29383556134240677589933676479674591580917833333552622040359156512591692573028
def addSlope : F := 51352876253922292050326070606498567023386155328912034665810991523381496495365
def outX : F := 33652555203852847325435703373215766219990032473577316466385438734209534304630
def outY : F := 29383556134240677589933676479674591580917833333552622040359156512591692573028

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) • base) + ((25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep243.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (12885287475909511778264964871177193019118005193927893854938256900211065153502 : Int)) * (46067497230238696504739105574094414911860075604725132392732525126513696448270 : Int) =
        (1 : Int) + (22640718520470933556659647505330435489847710204879232083872334675625426624583 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13663030713446832055873942527930062764211151458337472355627542775893161108166 : Int) * ((2 : Int) * (12885287475909511778264964871177193019118005193927893854938256900211065153502 : Int)) =
        (3 : Int) * (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) + (-40964 : Int) * (-40964 : Int) + (-73135047858009910204531974181522286997021495235169207842521810911892927973912 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int) =
        (13663030713446832055873942527930062764211151458337472355627542775893161108166 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) - (37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) + (-3560127635004085623368458642854980067325670489892567708565816267700270867004 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27191964069339054588275470758277425230860864720520810368792178922275143880032 : Int) =
        (13663030713446832055873942527930062764211151458337472355627542775893161108166 : Int) * ((37358642005473444203882245883233558319416201610318860048502099871968502082644 : Int) - (24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int)) - (12885287475909511778264964871177193019118005193927893854938256900211065153502 : Int) + (-3261992295775611805964216088694777828347407492669476968272847208429730721802 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) • base) + ((25603454675354585195042842045012678631663754944813739380333434228094465836 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34988582750249674678368436408278459158517592504656393777015014697445473545834 : Int) =
        (1 : Int) + (-9902480186804774388258023742463483880601170412655033652427857591581947129359 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (51352876253922292050326070606498567023386155328912034665810991523381496495365 : Int) * ((24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (27191964069339054588275470758277425230860864720520810368792178922275143880032 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-14533907911324991653210160244295185038893419781788167612732558374858553251117 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int) =
        (51352876253922292050326070606498567023386155328912034665810991523381496495365 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-50292245351930652056966031155540453318593211610785833776972177331864539603792 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (29383556134240677589933676479674591580917833333552622040359156512591692573028 : Int) =
        (51352876253922292050326070606498567023386155328912034665810991523381496495365 : Int) * ((24839792825461396775626266320921639093208782415654540471784566096822018176584 : Int) - (33652555203852847325435703373215766219990032473577316466385438734209534304630 : Int)) - (27191964069339054588275470758277425230860864720520810368792178922275143880032 : Int) + (8630745541316674401109311574557975677626169232716986403117611415814600033450 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (51206909350709170390085684090025357263327509889627478760666868456188931673 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (51206909350709170390085684090025357263327509889627478760666868456188931673 : Nat) = 25603454675354585195042842045012678631663754944813739380333434228094465836 + 25603454675354585195042842045012678631663754944813739380333434228094465836 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep244
