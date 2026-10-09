import ShielddSecurity.ConcretePointTraceStep189
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep190
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 6969037676750295985428532703249517442761901418630701637489494608086960821417
def inputY : F := 21465722024821691164279013471078412042773282418695313593283447497924060391024
def doubleX : F := 46232636813242975200694222752947787298657322404722802651857447643735279016707
def doubleY : F := 36162959617587609228251872809098995771168515068556859207912079638624736142087
def doubleSlope : F := 42167233972012487516003416695053133745916060093341269415506352123206748330443
def outX : F := 46232636813242975200694222752947787298657322404722802651857447643735279016707
def outY : F := 36162959617587609228251872809098995771168515068556859207912079638624736142087

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1421277244526263649762201193572235182286598028911991341579 : Nat) • base) + ((1421277244526263649762201193572235182286598028911991341579 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep189.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21465722024821691164279013471078412042773282418695313593283447497924060391024 : Int)) * (38373704391810618537979697297933939523131656399570093365445142285583290547716 : Int) =
        (1 : Int) + (31418156702304100230872709193707682370289362627091029595005463065619991589759 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (42167233972012487516003416695053133745916060093341269415506352123206748330443 : Int) * ((2 : Int) * (21465722024821691164279013471078412042773282418695313593283447497924060391024 : Int)) =
        (3 : Int) * (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) + (-40964 : Int) * (-40964 : Int) + (31745399156938441180336330101727309996851672744067516303571542628124462913901 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) =
        (42167233972012487516003416695053133745916060093341269415506352123206748330443 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) - (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) + (-33909525013399663650847121295617915553038936128475966762885182672012635783852 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36162959617587609228251872809098995771168515068556859207912079638624736142087 : Int) =
        (42167233972012487516003416695053133745916060093341269415506352123206748330443 : Int) * ((6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) - (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int)) - (21465722024821691164279013471078412042773282418695313593283447497924060391024 : Int) + (31574515841344682380720249578401838627862927339380602150646702384137047809237 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2842554489052527299524402387144470364573196057823982683158 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2842554489052527299524402387144470364573196057823982683158 : Nat) = 1421277244526263649762201193572235182286598028911991341579 + 1421277244526263649762201193572235182286598028911991341579 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep190
