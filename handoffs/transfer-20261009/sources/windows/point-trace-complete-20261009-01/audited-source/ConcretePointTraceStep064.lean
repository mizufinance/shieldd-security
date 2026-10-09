import ShielddSecurity.ConcretePointTraceStep063
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep064
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 37176356966639490230540366278156516828193009809942079545520782342339950640546
def inputY : F := 2202401624001785122677968684357280230372150033801081057322749784389811960889
def doubleX : F := 39614047561310823587481091238856254897733127891130228102422155395408029290677
def doubleY : F := 15821335370192190507577400118331906245328277898888636965530052816553626505425
def doubleSlope : F := 31375963122617576316707214985307482683074231234755994518666417243589330647206
def outX : F := 39614047561310823587481091238856254897733127891130228102422155395408029290677
def outY : F := 15821335370192190507577400118331906245328277898888636965530052816553626505425

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((16707033718928898704 : Nat) • base) + ((16707033718928898704 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep063.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2202401624001785122677968684357280230372150033801081057322749784389811960889 : Int)) * (3110923978835344379302575241716318543340549521177886354262921045752066486359 : Int) =
        (1 : Int) + (261328870749283488535675990939528260832780481110824571109708082912322047677 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (31375963122617576316707214985307482683074231234755994518666417243589330647206 : Int) * ((2 : Int) * (2202401624001785122677968684357280230372150033801081057322749784389811960889 : Int)) =
        (3 : Int) * (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) + (-40964 : Int) * (-40964 : Int) + (-76436973623023388725825468654403456292124991736897439423968334979717100465040 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) =
        (31375963122617576316707214985307482683074231234755994518666417243589330647206 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) - (37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) + (-18774380299441410864353195465895403180126345653868229616535762178922400694195 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15821335370192190507577400118331906245328277898888636965530052816553626505425 : Int) =
        (31375963122617576316707214985307482683074231234755994518666417243589330647206 : Int) * ((37176356966639490230540366278156516828193009809942079545520782342339950640546 : Int) - (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int)) - (2202401624001785122677968684357280230372150033801081057322749784389811960889 : Int) + (1458636667116053318286322712662239969210758501896687840407862260638253323100 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (33414067437857797408 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (33414067437857797408 : Nat) = 16707033718928898704 + 16707033718928898704 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep064
