import ShielddSecurity.ConcretePointTraceStep158
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep159
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32497163865107864410659142184213987361103789369805661642600027875981897493121
def inputY : F := 16418898027196858049893700505641343202218381678638333858829041735355981185034
def doubleX : F := 6174854229412295567172660711483373808468036944033653047592785988030350830750
def doubleY : F := 15755458460230156283510646336334208568769923356930467633590082181634813809287
def doubleSlope : F := 40745777219683525665076470396368527995721579638611459233892535583346241388817
def outX : F := 6174854229412295567172660711483373808468036944033653047592785988030350830750
def outY : F := 15755458460230156283510646336334208568769923356930467633590082181634813809287

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((661833791307296440825891305493300399876478141598 : Nat) • base) + ((661833791307296440825891305493300399876478141598 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep158.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16418898027196858049893700505641343202218381678638333858829041735355981185034 : Int)) * (21912883191909072124939484026548579733173208241707465181589592490479119384242 : Int) =
        (1 : Int) + (13722871732691174873543175744300547600772956047619038291949291069034627458535 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40745777219683525665076470396368527995721579638611459233892535583346241388817 : Int) * ((2 : Int) * (16418898027196858049893700505641343202218381678638333858829041735355981185034 : Int)) =
        (3 : Int) * (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) + (-40964 : Int) * (-40964 : Int) + (-34903497830383707549448189709448391317037719938651758563782438610628559864239 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) =
        (40745777219683525665076470396368527995721579638611459233892535583346241388817 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) - (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) + (-31661879499317148856047125809589838798318250844202247824949042776060803572105 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15755458460230156283510646336334208568769923356930467633590082181634813809287 : Int) =
        (40745777219683525665076470396368527995721579638611459233892535583346241388817 : Int) * ((32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) - (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int)) - (16418898027196858049893700505641343202218381678638333858829041735355981185034 : Int) + (-20453991866094558292304932342073197309195368106807265068428285539512918715522 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1323667582614592881651782610986600799752956283196 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1323667582614592881651782610986600799752956283196 : Nat) = 661833791307296440825891305493300399876478141598 + 661833791307296440825891305493300399876478141598 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep159
