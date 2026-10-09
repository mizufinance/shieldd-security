import ShielddSecurity.ConcretePointTraceStep044
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep045
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 50620992677045785735709756883586794796736072343914480114465453523438753032352
def inputY : F := 31034416229820277960423439615363864005689939766264200426733973844276068445802
def doubleX : F := 32510813837869581354012590503628603748655675077490635625567946577528389800880
def doubleY : F := 44037891352928711476637246091610747034246896357656061059278012919965223845366
def doubleSlope : F := 10020292900731501314978336660921612015039985228093924844273973020553834120205
def outX : F := 32510813837869581354012590503628603748655675077490635625567946577528389800880
def outY : F := 44037891352928711476637246091610747034246896357656061059278012919965223845366

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((31866137922151 : Nat) • base) + ((31866137922151 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep044.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (31034416229820277960423439615363864005689939766264200426733973844276068445802 : Int)) * (41249026316200497138781384275461613477947005059692395643699547602863140182506 : Int) =
        (1 : Int) + (48826855563918628503791442784374523959533629844872368763349120575209725398471 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10020292900731501314978336660921612015039985228093924844273973020553834120205 : Int) * ((2 : Int) * (31034416229820277960423439615363864005689939766264200426733973844276068445802 : Int)) =
        (3 : Int) * (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) + (-40964 : Int) * (-40964 : Int) + (-134745663993955381594094673160316839688664180289985277799234981820388117977932 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) =
        (10020292900731501314978336660921612015039985228093924844273973020553834120205 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) - (50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) + (-1914839210390055063825809812314343565100357457383865026471631419543298425793 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44037891352928711476637246091610747034246896357656061059278012919965223845366 : Int) =
        (10020292900731501314978336660921612015039985228093924844273973020553834120205 : Int) * ((50620992677045785735709756883586794796736072343914480114465453523438753032352 : Int) - (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int)) - (31034416229820277960423439615363864005689939766264200426733973844276068445802 : Int) + (-3460785117957907033577389562971648852202732598573177466482473528509856965584 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (63732275844302 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (63732275844302 : Nat) = 31866137922151 + 31866137922151 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep045
