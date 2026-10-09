import ShielddSecurity.ConcretePointTraceStep226
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep227
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48656421800279876367292632588916888997534564130984080997975354180202588755998
def inputY : F := 10682480107917171582802857667287591259136657361618992850795392468437179503872
def doubleX : F := 24188445313190595005135390897078619891378705797914974064515670624335802659725
def doubleY : F := 14638837250991371995610211486798395067626841606728948335074620493566100466149
def doubleSlope : F := 24643566653913507886696567981353666164506513583356566072147581184822753494593
def outX : F := 24188445313190595005135390897078619891378705797914974064515670624335802659725
def outY : F := 14638837250991371995610211486798395067626841606728948335074620493566100466149

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((195338857081257516441672073707677296689329185064802088778178666901355 : Nat) • base) + ((195338857081257516441672073707677296689329185064802088778178666901355 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep226.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (10682480107917171582802857667287591259136657361618992850795392468437179503872 : Int)) * (10507675830036531109128411536105905578337160448358547008088734520644416260913 : Int) =
        (1 : Int) + (4281345077579785654265255822996281028692424153293659468292502771658118138367 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24643566653913507886696567981353666164506513583356566072147581184822753494593 : Int) * ((2 : Int) * (10682480107917171582802857667287591259136657361618992850795392468437179503872 : Int)) =
        (3 : Int) * (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) + (-40964 : Int) * (-40964 : Int) + (-125407143565756328895608069956440836959836152802467313155178753338913157529276 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) =
        (24643566653913507886696567981353666164506513583356566072147581184822753494593 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) - (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) + (-11581867860459836140025268176414488626824645034837660675314125926785084569792 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (14638837250991371995610211486798395067626841606728948335074620493566100466149 : Int) =
        (24643566653913507886696567981353666164506513583356566072147581184822753494593 : Int) * ((48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) - (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int)) - (10682480107917171582802857667287591259136657361618992850795392468437179503872 : Int) + (-11499344817496356031151149885590788333760844719243362757562212391561872633836 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (390677714162515032883344147415354593378658370129604177556357333802710 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (390677714162515032883344147415354593378658370129604177556357333802710 : Nat) = 195338857081257516441672073707677296689329185064802088778178666901355 + 195338857081257516441672073707677296689329185064802088778178666901355 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep227
