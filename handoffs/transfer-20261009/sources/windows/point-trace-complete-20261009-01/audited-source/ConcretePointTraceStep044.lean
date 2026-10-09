import ShielddSecurity.ConcretePointTraceStep043
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep044
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41420983510373286248097911444478048782904202611705300317720624829134874036356
def inputY : F := 26916796564446889899868763747739476696533691125895817157306401920241054741533
def doubleX : F := 36300224032144193748434529123768113971165155054458711205788401585706231746091
def doubleY : F := 51684731644673983574621257119354616556170446398547402021425406237330823560756
def doubleSlope : F := 12624377221542720950910236280918627411728065807988366556541842736972997693819
def addX : F := 50620992677045785735709756883586794796736072343914480114465453523438753032352
def addY : F := 31034416229820277960423439615363864005689939766264200426733973844276068445802
def addSlope : F := 28132298066970093619903685794227017494544314592727729012545239982147461238940
def outX : F := 50620992677045785735709756883586794796736072343914480114465453523438753032352
def outY : F := 31034416229820277960423439615363864005689939766264200426733973844276068445802

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((15933068961075 : Nat) • base) + ((15933068961075 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep043.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (26916796564446889899868763747739476696533691125895817157306401920241054741533 : Int)) * (15520859735914740028963238987130149548358383451143451484466762577146692275783 : Int) =
        (1 : Int) + (15934580003543405762048989249395204158142441810275933521006357452568970564629 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (12624377221542720950910236280918627411728065807988366556541842736972997693819 : Int) * ((2 : Int) * (26916796564446889899868763747739476696533691125895817157306401920241054741533 : Int)) =
        (3 : Int) * (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) + (-40964 : Int) * (-40964 : Int) + (-85198883839148020932711730282257299337975359703938102208996860805062070736418 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int) =
        (12624377221542720950910236280918627411728065807988366556541842736972997693819 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) - (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) + (-3039424815539434054780941430780768576779823152691857080986907781027628741102 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (51684731644673983574621257119354616556170446398547402021425406237330823560756 : Int) =
        (12624377221542720950910236280918627411728065807988366556541842736972997693819 : Int) * ((41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) - (36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int)) - (26916796564446889899868763747739476696533691125895817157306401920241054741533 : Int) + (-1232865840382128575661117304379611454889575029387488348609530653082041155442 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((15933068961075 : Nat) • base) + ((15933068961075 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (48711050319727833417865665490267912213250400872297723071175731106395399504582 : Int) =
        (1 : Int) + (-3139887272045915480945730632111819651674202574175110562459102938783764190065 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (28132298066970093619903685794227017494544314592727729012545239982147461238940 : Int) * ((36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (51684731644673983574621257119354616556170446398547402021425406237330823560756 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-1813392321744025439604096916346859380857467560464804416600942473105036877930 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) =
        (28132298066970093619903685794227017494544314592727729012545239982147461238940 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-15093219897362848687035259060537981376726639150745512440101085291176807711034 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (31034416229820277960423439615363864005689939766264200426733973844276068445802 : Int) =
        (28132298066970093619903685794227017494544314592727729012545239982147461238940 : Int) * ((36300224032144193748434529123768113971165155054458711205788401585706231746091 : Int) - (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int)) - (51684731644673983574621257119354616556170446398547402021425406237330823560756 : Int) + (7683215560357459689585850893255626487297678599649832511165115286523791367146 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (31866137922151 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (31866137922151 : Nat) = 15933068961075 + 15933068961075 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep044
