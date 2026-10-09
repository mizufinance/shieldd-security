import ShielddSecurity.ConcretePointTraceStep229
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep230
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 40626827023203268955061382922832853403565936910713743647620890213540648366764
def inputY : F := 44639586313569380652127228493501711701688349631168306188810122534468419439433
def doubleX : F := 9555897669341657420113388484386812210961631758877333158449574013682423859120
def doubleY : F := 11480505396806390662481623691729220198869199394865413138002635217409831814079
def doubleSlope : F := 3733246481087940949586174530403271179940591843432891086451389246893602156272
def addX : F := 34877913436063020738398167695095977309175058417401779269709656337699354728823
def addY : F := 42166255922519058322045855362693485245378823701561069765451221737270197566327
def addSlope : F := 24634938545143873362969971431356599600213329450666541740491183196041294536417
def outX : F := 34877913436063020738398167695095977309175058417401779269709656337699354728823
def outY : F := 42166255922519058322045855362693485245378823701561069765451221737270197566327

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) • base) + ((1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep229.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (44639586313569380652127228493501711701688349631168306188810122534468419439433 : Int)) * (18583423685650574397521024372135258523701810665628952297300589160491906189428 : Int) =
        (1 : Int) + (31640793363195050508881138900124341696157538378796699016599348813337038113319 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (3733246481087940949586174530403271179940591843432891086451389246893602156272 : Int) * ((2 : Int) * (44639586313569380652127228493501711701688349631168306188810122534468419439433 : Int)) =
        (3 : Int) * (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) + (-40964 : Int) * (-40964 : Int) + (-88075502686868528513639142081494920792305225910383621987484523932249187834656 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int) =
        (3733246481087940949586174530403271179940591843432891086451389246893602156272 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) - (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) + (-265793776531964848588411270104107198268762276421737202322954745109469918208 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (11480505396806390662481623691729220198869199394865413138002635217409831814079 : Int) =
        (3733246481087940949586174530403271179940591843432891086451389246893602156272 : Int) * ((40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) - (9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int)) - (44639586313569380652127228493501711701688349631168306188810122534468419439433 : Int) + (-2212138870325562773275210758934382728209361938112686519401872130754096563512 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) • base) + ((1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (40658703521873446951838145077488783137688564809185269288802156685546382401189 : Int) =
        (1 : Int) + (-23358350339501216081408894289397230701287455863264506391536447584633319953616 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (24634938545143873362969971431356599600213329450666541740491183196041294536417 : Int) * ((9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (11480505396806390662481623691729220198869199394865413138002635217409831814079 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-14152726852689340389294339517646488227534380739960166955558087974096442566808 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) =
        (24634938545143873362969971431356599600213329450666541740491183196041294536417 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-11573759284004452428823505177145261183095267547788176387471199840057345702287 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42166255922519058322045855362693485245378823701561069765451221737270197566327 : Int) =
        (24634938545143873362969971431356599600213329450666541740491183196041294536417 : Int) * ((9555897669341657420113388484386812210961631758877333158449574013682423859120 : Int) - (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int)) - (11480505396806390662481623691729220198869199394865413138002635217409831814079 : Int) + (11896555557982899119228081209493461833334029919807320347826703572873761583389 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) = 1562710856650060131533376589661418373514633480518416710225429335210843 + 1562710856650060131533376589661418373514633480518416710225429335210843 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep230
