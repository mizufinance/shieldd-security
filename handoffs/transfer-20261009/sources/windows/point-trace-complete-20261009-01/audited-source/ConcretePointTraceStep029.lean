import ShielddSecurity.ConcretePointTraceStep028
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep029
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11588435951221175233044980985051644150460896435316666909091959764933412287874
def inputY : F := 15248497707848093284485582568996720271841207247011320331443362226385948315421
def doubleX : F := 13924569977804592562066830024495883326000268657175268647155346940333209671786
def doubleY : F := 17774238217443435602138164255448760128240290343059710938988945113554381620726
def doubleSlope : F := 20740017251895956584606259670435945020082162097342088444789617072498390999891
def addX : F := 21096557341129318036935165035116531548878001934455463800463554823722073269553
def addY : F := 1688460704591636169008746998165317674695270965295441312037947241562229018264
def addSlope : F := 48116697356029120911249007718577974973675764088457472384237786829977455036694
def outX : F := 21096557341129318036935165035116531548878001934455463800463554823722073269553
def outY : F := 1688460704591636169008746998165317674695270965295441312037947241562229018264

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((486238676 : Nat) • base) + ((486238676 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep028.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15248497707848093284485582568996720271841207247011320331443362226385948315421 : Int)) * (26336492253311452058040619482688314974001395482893582646389553262462022695527 : Int) =
        (1 : Int) + (15317449758057262516792535503226319322250193359929212425962503893598486809941 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (20740017251895956584606259670435945020082162097342088444789617072498390999891 : Int) * ((2 : Int) * (15248497707848093284485582568996720271841207247011320331443362226385948315421 : Int)) =
        (3 : Int) * (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) + (-40964 : Int) * (-40964 : Int) + (4379304567701666277949142787231551421997693150902012862271831707362302808274 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int) =
        (20740017251895956584606259670435945020082162097342088444789617072498390999891 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) - (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) + (-8203320992971425617754985672824339619968212530781145171405941931588428679555 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (17774238217443435602138164255448760128240290343059710938988945113554381620726 : Int) =
        (20740017251895956584606259670435945020082162097342088444789617072498390999891 : Int) * ((11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) - (13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int)) - (15248497707848093284485582568996720271841207247011320331443362226385948315421 : Int) + (924013566136967617479240427939871666971707762621582141828373003588506787403 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((486238676 : Nat) • base) + ((486238676 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (13146404337153882185122006276869100957863366542804659439907367919307494761489 : Int) =
        (1 : Int) + (-6457298092007703203348338587641340112324683336007699890854366884526560329018 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (48116697356029120911249007718577974973675764088457472384237786829977455036694 : Int) * ((13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (17774238217443435602138164255448760128240290343059710938988945113554381620726 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-23634132197858784598157046802950548035278270321921795481775074787333802929746 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) =
        (48116697356029120911249007718577974973675764088457472384237786829977455036694 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-44153293078818686269019386040448373380787559541357729028365134648520412522814 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (1688460704591636169008746998165317674695270965295441312037947241562229018264 : Int) =
        (48116697356029120911249007718577974973675764088457472384237786829977455036694 : Int) * ((13924569977804592562066830024495883326000268657175268647155346940333209671786 : Int) - (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int)) - (17774238217443435602138164255448760128240290343059710938988945113554381620726 : Int) + (6581226007000284540751581707973708221734155287543592024195013985661956779176 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (972477353 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (972477353 : Nat) = 486238676 + 486238676 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep029
