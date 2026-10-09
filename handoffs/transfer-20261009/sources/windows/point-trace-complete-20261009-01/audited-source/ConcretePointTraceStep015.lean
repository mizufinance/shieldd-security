import ShielddSecurity.ConcretePointTraceStep014
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep015
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 16563918511737849350055151229619595918806303779926919627409058753629890695841
def inputY : F := 7830866387738348311722657341583576969185386966220487808300292672582758839180
def doubleX : F := 20042910187368270507285227526011118798592273114592396098844487530027360585091
def doubleY : F := 1339592176759286466458837530902249211863630390661947158387472582131683033556
def doubleSlope : F := 32372434785408170319023935042591802176263553232281325736443001993683753098205
def addX : F := 46036438912242758694663670900035586573714113806566576077092645583543283979915
def addY : F := 24294495313598841576630948218175267399274674983910386354687952540563966479383
def addSlope : F := 51859875918555556116151245957854696405780785798726994532551957619401312455381
def outX : F := 46036438912242758694663670900035586573714113806566576077092645583543283979915
def outY : F := 24294495313598841576630948218175267399274674983910386354687952540563966479383

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((29677 : Nat) • base) + ((29677 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep014.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7830866387738348311722657341583576969185386966220487808300292672582758839180 : Int)) * (42256764040570711559695387373483445319636789301831526949399033867756681211626 : Int) =
        (1 : Int) + (12621399836456504784155230572997582926674784789325655344943315188992974556143 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (32372434785408170319023935042591802176263553232281325736443001993683753098205 : Int) * ((2 : Int) * (7830866387738348311722657341583576969185386966220487808300292672582758839180 : Int)) =
        (3 : Int) * (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) + (-40964 : Int) * (-40964 : Int) + (-6027967787973621727054034496335330092738524424363736769982810207345512573451 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int) =
        (32372434785408170319023935042591802176263553232281325736443001993683753098205 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) - (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) + (-19985830892217637305989070105112427872799043737869009452843972387489085321740 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1339592176759286466458837530902249211863630390661947158387472582131683033556 : Int) =
        (32372434785408170319023935042591802176263553232281325736443001993683753098205 : Int) * ((16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) - (20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int)) - (7830866387738348311722657341583576969185386966220487808300292672582758839180 : Int) + (2147831627910893696907566925524916319529501624469763544811048280945973196922 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((29677 : Nat) • base) + ((29677 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (30282476069145689579003616763772305790136937431382183316780823767661144721323 : Int) =
        (1 : Int) + (-11340825407818568480408185533347682242202697160508259087582692472823919778609 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (51859875918555556116151245957854696405780785798726994532551957619401312455381 : Int) * ((20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (1339592176759286466458837530902249211863630390661947158387472582131683033556 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-19421588813297632008444226165647027006892507356230362324589252119838151082874 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int) =
        (51859875918555556116151245957854696405780785798726994532551957619401312455381 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-51290203916797811886606978345227716260736726076426728909006466666370742030880 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (24294495313598841576630948218175267399274674983910386354687952540563966479383 : Int) =
        (51859875918555556116151245957854696405780785798726994532551957619401312455381 : Int) * ((20042910187368270507285227526011118798592273114592396098844487530027360585091 : Int) - (46036438912242758694663670900035586573714113806566576077092645583543283979915 : Int)) - (1339592176759286466458837530902249211863630390661947158387472582131683033556 : Int) + (25707994190146679043622267330410226750418547763328092291406303424090450905491 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (59355 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (59355 : Nat) = 29677 + 29677 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep015
