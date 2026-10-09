import ShielddSecurity.ConcretePointTraceStep111
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep112
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3937438753608230034618003978372154230051041743589846586894599496688287252225
def inputY : F := 35997831797499231780797956312155720429329632056191926696093734804943318124453
def doubleX : F := 38929614553413756590514539650029974016595123022111806861934027841389540720894
def doubleY : F := 19896896673454146348019811732480833133114871477217096672963686910540904816695
def doubleSlope : F := 37263361741210072711991460306876525969569333191775115040880260872940672226181
def addX : F := 4507714052907436369009784069803537723757080562639008376807807606686726018950
def addY : F := 33944708627911101349340602174293675074636939729612380276147006734932065595466
def addSlope : F := 41928400200787714867500139312586129925027701558677198893363529929697372704213
def outX : F := 4507714052907436369009784069803537723757080562639008376807807606686726018950
def outY : F := 33944708627911101349340602174293675074636939729612380276147006734932065595466

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4702611926939656263086613602505539 : Nat) • base) + ((4702611926939656263086613602505539 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep111.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (35997831797499231780797956312155720429329632056191926696093734804943318124453 : Int)) * (39053011629500929599859986878898310293939829306447166149861080178756279612438 : Int) =
        (1 : Int) + (53620683897402791520302030334664251715989564516032613867255580105916921305179 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (37263361741210072711991460306876525969569333191775115040880260872940672226181 : Int) * ((2 : Int) * (35997831797499231780797956312155720429329632056191926696093734804943318124453 : Int)) =
        (3 : Int) * (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) + (-40964 : Int) * (-40964 : Int) + (50276460070875595596547270490546152264537514039235465851517886023583860057455 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int) =
        (37263361741210072711991460306876525969569333191775115040880260872940672226181 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) - (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) + (-26481070900766879838112440471987685382645717651441996930271088315405917094945 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (19896896673454146348019811732480833133114871477217096672963686910540904816695 : Int) =
        (37263361741210072711991460306876525969569333191775115040880260872940672226181 : Int) * ((3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) - (38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int)) - (35997831797499231780797956312155720429329632056191926696093734804943318124453 : Int) + (24867060968951058390072411529912034155172310210841070125359837682092808828749 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((4702611926939656263086613602505539 : Nat) • base) + ((4702611926939656263086613602505539 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (30731162182086031896372370353391022688021336801582539574910824293032237159734 : Int) =
        (1 : Int) + (-439903306717932488009749361920134829871825953947469083608081070402200666479 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (41928400200787714867500139312586129925027701558677198893363529929697372704213 : Int) * ((38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (19896896673454146348019811732480833133114871477217096672963686910540904816695 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-600186930270768274878435454108458766664835176788620909987766241289959069062 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int) =
        (41928400200787714867500139312586129925027701558677198893363529929697372704213 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-33526488068065025193187004856406453158624522817314825251870350420860624147370 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (33944708627911101349340602174293675074636939729612380276147006734932065595466 : Int) =
        (41928400200787714867500139312586129925027701558677198893363529929697372704213 : Int) * ((38929614553413756590514539650029974016595123022111806861934027841389540720894 : Int) - (4507714052907436369009784069803537723757080562639008376807807606686726018950 : Int)) - (19896896673454146348019811732480833133114871477217096672963686910540904816695 : Int) + (-27524194361908076008107199043324619711594304270419636583013189911254794946647 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (9405223853879312526173227205011079 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (9405223853879312526173227205011079 : Nat) = 4702611926939656263086613602505539 + 4702611926939656263086613602505539 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep112
