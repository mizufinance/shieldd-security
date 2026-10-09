import ShielddSecurity.ConcretePointTraceStep152
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep153
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31377089600692335345539465202229641755185991732207410461614767105978359494774
def inputY : F := 18540913326032609200191315319724757365728071065355860251325188698499579073829
def doubleX : F := 343511366769113804656546802764779546722161162829979512415871444728095558163
def doubleY : F := 44750022144722540566978321980808116286834314338329035391606952686135637804525
def doubleSlope : F := 812775914564578977384697224093707933580363884377477301766013425048348035540
def outX : F := 343511366769113804656546802764779546722161162829979512415871444728095558163
def outY : F := 44750022144722540566978321980808116286834314338329035391606952686135637804525

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((10341152989176506887904551648332818748069970962 : Nat) • base) + ((10341152989176506887904551648332818748069970962 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep152.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18540913326032609200191315319724757365728071065355860251325188698499579073829 : Int)) * (5800161006696165084272052979298192710998669362079030555317998868703785197098 : Int) =
        (1 : Int) + (4101782687636006948500911395626780612112567924432476907638076548777887046691 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (812775914564578977384697224093707933580363884377477301766013425048348035540 : Int) * ((2 : Int) * (18540913326032609200191315319724757365728071065355860251325188698499579073829 : Int)) =
        (3 : Int) * (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) + (-40964 : Int) * (-40964 : Int) + (-55752402912987756362457944096181272720407914719168146594976436009311909010580 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) =
        (812775914564578977384697224093707933580363884377477301766013425048348035540 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) - (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) + (-12598334348191757728303681321017645333010740185505551399015634360279899289 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44750022144722540566978321980808116286834314338329035391606952686135637804525 : Int) =
        (812775914564578977384697224093707933580363884377477301766013425048348035540 : Int) * ((31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) - (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int)) - (18540913326032609200191315319724757365728071065355860251325188698499579073829 : Int) + (-481032210238639473082317113396230421229419278017098124104326487333894982122 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (20682305978353013775809103296665637496139941924 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (20682305978353013775809103296665637496139941924 : Nat) = 10341152989176506887904551648332818748069970962 + 10341152989176506887904551648332818748069970962 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep153
