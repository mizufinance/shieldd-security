import ShielddSecurity.ConcretePointTraceStep089
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep090
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32669888196170295129130102360412865853502054249683973932511754814273944284330
def inputY : F := 2233563748692398574704302608170879641645972072331674571535663269072270535137
def doubleX : F := 48473148037231391718888351392282094392020086869745349554027605405564742908252
def doubleY : F := 32984785281461483103409986687486196095303763963871799240315008732312122778749
def doubleSlope : F := 19837254582766971522615117154292911015442435006956430677292187690448450698789
def outX : F := 48473148037231391718888351392282094392020086869745349554027605405564742908252
def outY : F := 32984785281461483103409986687486196095303763963871799240315008732312122778749

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1121190053687013688823369408 : Nat) • base) + ((1121190053687013688823369408 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep089.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2233563748692398574704302608170879641645972072331674571535663269072270535137 : Int)) * (5690386729994536609962763559447243821918179643982670970338980616430466958183 : Int) =
        (1 : Int) + (484776557031137214288242177536924157217627311922560979327684047233112537357 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19837254582766971522615117154292911015442435006956430677292187690448450698789 : Int) * ((2 : Int) * (2233563748692398574704302608170879641645972072331674571535663269072270535137 : Int)) =
        (3 : Int) * (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) + (-40964 : Int) * (-40964 : Int) + (-59374411668223064704462385422184013857847323706949274897057718537993962766610 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) =
        (19837254582766971522615117154292911015442435006956430677292187690448450698789 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) - (32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) + (-7504722064182886768261276928400745862105916950075049769612711923320524119729 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (32984785281461483103409986687486196095303763963871799240315008732312122778749 : Int) =
        (19837254582766971522615117154292911015442435006956430677292187690448450698789 : Int) * ((32669888196170295129130102360412865853502054249683973932511754814273944284330 : Int) - (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int)) - (2233563748692398574704302608170879641645972072331674571535663269072270535137 : Int) + (5978603153999747035427951389951645002083312197013506797020513763672401854488 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2242380107374027377646738816 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2242380107374027377646738816 : Nat) = 1121190053687013688823369408 + 1121190053687013688823369408 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep090
