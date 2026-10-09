import ShielddSecurity.ConcretePointTraceStep132
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep133
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 8750949743486244879832974919727339812249473397508506460414106552978630048253
def inputY : F := 29983144448755360265655030035249929695952211445658121200202837882361415553500
def doubleX : F := 28141117652816364073168398286702188571953846789078042185657060418471040761009
def doubleY : F := 21196235059881308502772151712889894369303163019760520045346368204776985916393
def doubleSlope : F := 16152805644359930398193371719095188724726925564287078826834761738042369022690
def addX : F := 44319826743251418605552096911184252296135959549460594984336300895864160026666
def addY : F := 4066007365998513237822314428336016727463879784035898691569132468071648916250
def addSlope : F := 15276964468978465832006946367412904489238492859726347315479209364279737438835
def outX : F := 44319826743251418605552096911184252296135959549460594984336300895864160026666
def outY : F := 4066007365998513237822314428336016727463879784035898691569132468071648916250

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((9862092007805354011444617889721697567052 : Nat) • base) + ((9862092007805354011444617889721697567052 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep132.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29983144448755360265655030035249929695952211445658121200202837882361415553500 : Int)) * (37842088717059509260668733959284176699312191088054897809454324042630342986323 : Int) =
        (1 : Int) + (43276661577851890094792539176719756927708232881448082831965710194473875424423 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16152805644359930398193371719095188724726925564287078826834761738042369022690 : Int) * ((2 : Int) * (29983144448755360265655030035249929695952211445658121200202837882361415553500 : Int)) =
        (3 : Int) * (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) + (-40964 : Int) * (-40964 : Int) + (14091238928848207004457643570050185717691090081412147604931627039583238810645 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int) =
        (16152805644359930398193371719095188724726925564287078826834761738042369022690 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) - (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) + (-4975851538914228128538970461125294838996333120889343187678976420616081030881 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21196235059881308502772151712889894369303163019760520045346368204776985916393 : Int) =
        (16152805644359930398193371719095188724726925564287078826834761738042369022690 : Int) * ((8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) - (28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int)) - (29983144448755360265655030035249929695952211445658121200202837882361415553500 : Int) + (5973116928150147728186211195995591250182946254887071867884318480070160314541 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((9862092007805354011444617889721697567052 : Nat) • base) + ((9862092007805354011444617889721697567052 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (16304982834924406811543127215533513761230122993725538709383753274865771131230 : Int) =
        (1 : Int) + (-3588091657127745262773529820827031567279739118202574315452627712071258821117 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (15276964468978465832006946367412904489238492859726347315479209364279737438835 : Int) * ((28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (21196235059881308502772151712889894369303163019760520045346368204776985916393 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-3361864855200429439061161931187119858945954646574240110466550607309091313349 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int) =
        (15276964468978465832006946367412904489238492859726347315479209364279737438835 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4450877240190333872681454575011630074073177814412833346664902004500956281795 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (4066007365998513237822314428336016727463879784035898691569132468071648916250 : Int) =
        (15276964468978465832006946367412904489238492859726347315479209364279737438835 : Int) * ((28141117652816364073168398286702188571953846789078042185657060418471040761009 : Int) - (44319826743251418605552096911184252296135959549460594984336300895864160026666 : Int)) - (21196235059881308502772151712889894369303163019760520045346368204776985916393 : Int) + (4713596618785154657935796608955584080588829943074258812269389144078662367326 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (19724184015610708022889235779443395134105 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (19724184015610708022889235779443395134105 : Nat) = 9862092007805354011444617889721697567052 + 9862092007805354011444617889721697567052 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep133
