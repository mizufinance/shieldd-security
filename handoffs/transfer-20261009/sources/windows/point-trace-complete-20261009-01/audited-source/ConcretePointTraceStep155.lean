import ShielddSecurity.ConcretePointTraceStep154
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep155
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 50748321365867478650009361082350517714146176131919743463351403407907922312422
def inputY : F := 41282394913594334171855457540884645471423541173374508094727234669777023316141
def doubleX : F := 939215188908647763325689519491375272522063326440993991698777949479306126673
def doubleY : F := 42830668157479982297648861985489534023646426128966425515552251568842400448372
def doubleSlope : F := 13116870221887354610249550407488577039289234376575306320369070585245585667939
def addX : F := 38076020991662553201322953943009372428476307892225054745374619609001492473576
def addY : F := 27959162627871934623588781124288107643747688433377718058143673159688839425130
def addSlope : F := 38124943372078886123090880053945310821914481392162346415070980172435624005164
def outX : F := 38076020991662553201322953943009372428476307892225054745374619609001492473576
def outY : F := 27959162627871934623588781124288107643747688433377718058143673159688839425130

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((41364611956706027551618206593331274992279883849 : Nat) • base) + ((41364611956706027551618206593331274992279883849 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep154.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (41282394913594334171855457540884645471423541173374508094727234669777023316141 : Int)) * (33058629744971692605493639352864848429688024444871589183680399493709929414271 : Int) =
        (1 : Int) + (52053652346842265737194583415155156343517463125242762879823353450021615146917 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13116870221887354610249550407488577039289234376575306320369070585245585667939 : Int) * ((2 : Int) * (41282394913594334171855457540884645471423541173374508094727234669777023316141 : Int)) =
        (3 : Int) * (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) + (-40964 : Int) * (-40964 : Int) + (-126691596337668232718639046856559549350539409242452751373892636362369683657166 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (939215188908647763325689519491375272522063326440993991698777949479306126673 : Int) =
        (13116870221887354610249550407488577039289234376575306320369070585245585667939 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) - (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) + (-3281194103144310948559452491710214022882101375141293604689849975574388085044 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (42830668157479982297648861985489534023646426128966425515552251568842400448372 : Int) =
        (13116870221887354610249550407488577039289234376575306320369070585245585667939 : Int) * ((50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) - (939215188908647763325689519491375272522063326440993991698777949479306126673 : Int)) - (41282394913594334171855457540884645471423541173374508094727234669777023316141 : Int) + (-12459782151234104567714430691612971214288628437957933561419574436159737688446 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((41364611956706027551618206593331274992279883849 : Nat) • base) + ((41364611956706027551618206593331274992279883849 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((939215188908647763325689519491375272522063326440993991698777949479306126673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12761836663381943939561341776728096287630887602755229889871549077452156059528 : Int) =
        (1 : Int) + (-9428778765976290036825033771630077249872036376907002886650650505693671435537 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (38124943372078886123090880053945310821914481392162346415070980172435624005164 : Int) * ((939215188908647763325689519491375272522063326440993991698777949479306126673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (42830668157479982297648861985489534023646426128966425515552251568842400448372 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-28167705480211364569430405974502040654183041833366442897033424514388365630882 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) =
        (38124943372078886123090880053945310821914481392162346415070980172435624005164 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (939215188908647763325689519491375272522063326440993991698777949479306126673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-27719787307254070544553799132056939338925884906103454162166527071833947890764 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (27959162627871934623588781124288107643747688433377718058143673159688839425130 : Int) =
        (38124943372078886123090880053945310821914481392162346415070980172435624005164 : Int) * ((939215188908647763325689519491375272522063326440993991698777949479306126673 : Int) - (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int)) - (42830668157479982297648861985489534023646426128966425515552251568842400448372 : Int) + (27001334744985991620422076802002503095019361404582288492669367443286644470738 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (82729223913412055103236413186662549984559767699 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (82729223913412055103236413186662549984559767699 : Nat) = 41364611956706027551618206593331274992279883849 + 41364611956706027551618206593331274992279883849 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep155
