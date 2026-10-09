import ShielddSecurity.ConcretePointTraceStep053
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep054
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45812760552077659989191185131240874644822596515033921572897724250895755032678
def inputY : F := 10951257807955434224754146695209291026437045154459722137853659197384939693887
def doubleX : F := 52371823613976216315044646586380754747426190286348320421970078554657120908094
def doubleY : F := 45780990347527404867396456744133972483692971817613879019339998568799777267190
def doubleSlope : F := 24674717892281058639812084368926960226547120024639280667980316812749828642782
def addX : F := 43466706957772582939888966516777287978387987349470947592029547584256902209833
def addY : F := 37042581758421943488030542698411988275685541495247962775714606686734430163555
def addSlope : F := 43764587983585890898833076606468090774823754644978863990104716268983229011748
def outX : F := 43466706957772582939888966516777287978387987349470947592029547584256902209833
def outY : F := 37042581758421943488030542698411988275685541495247962775714606686734430163555

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((16315462616141502 : Nat) • base) + ((16315462616141502 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep053.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (10951257807955434224754146695209291026437045154459722137853659197384939693887 : Int)) * (47149384837972828374066281718741858312567867780702729298276693016732225955471 : Int) =
        (1 : Int) + (19694343505191734731487816808206716931894449112584102821456683836581904682081 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24674717892281058639812084368926960226547120024639280667980316812749828642782 : Int) * ((2 : Int) * (10951257807955434224754146695209291026437045154459722137853659197384939693887 : Int)) =
        (3 : Int) * (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) + (-40964 : Int) * (-40964 : Int) + (-109771958130348409354369867911028122161288713781417111406623317532007886483544 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int) =
        (24674717892281058639812084368926960226547120024639280667980316812749828642782 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) - (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) + (-11611166992640736261560351148594863931390279824376585202011892268065401340034 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45780990347527404867396456744133972483692971817613879019339998568799777267190 : Int) =
        (24674717892281058639812084368926960226547120024639280667980316812749828642782 : Int) * ((45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) - (52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int)) - (10951257807955434224754146695209291026437045154459722137853659197384939693887 : Int) + (3086494316143329372924082761279256647149136908506430542266283980302081848453 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((16315462616141502 : Nat) • base) + ((16315462616141502 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (20704173001084736939841499895490637964401052847717776451643927851902290266520 : Int) =
        (1 : Int) + (5011251039167305720701772575220282032123634836993076606346095329216776649863 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (43764587983585890898833076606468090774823754644978863990104716268983229011748 : Int) * ((52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (45780990347527404867396456744133972483692971817613879019339998568799777267190 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (10592808367664980683520154485021835604199824262589194472489969681672060207168 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int) =
        (43764587983585890898833076606468090774823754644978863990104716268983229011748 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-36527266017324009747655370543866223716864167637240392477611660303466976297374 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (37042581758421943488030542698411988275685541495247962775714606686734430163555 : Int) =
        (43764587983585890898833076606468090774823754644978863990104716268983229011748 : Int) * ((52371823613976216315044646586380754747426190286348320421970078554657120908094 : Int) - (43466706957772582939888966516777287978387987349470947592029547584256902209833 : Int)) - (45780990347527404867396456744133972483692971817613879019339998568799777267190 : Int) + (-7432483201680102286849744862743112291199139729694888104287051324271401057691 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (32630925232283005 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (32630925232283005 : Nat) = 16315462616141502 + 16315462616141502 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep054
