import ShielddSecurity.ConcretePointTraceStep157
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep158
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32519754935291984064399895721098749478758911878471915533641312939975545696476
def inputY : F := 42956781121015365294969681217312514003994247563580404675698060438768365327098
def doubleX : F := 32497163865107864410659142184213987361103789369805661642600027875981897493121
def doubleY : F := 16418898027196858049893700505641343202218381678638333858829041735355981185034
def doubleSlope : F := 41832893090188087103652368949302522373463407721402170502318733053713670727961
def outX : F := 32497163865107864410659142184213987361103789369805661642600027875981897493121
def outY : F := 16418898027196858049893700505641343202218381678638333858829041735355981185034

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((330916895653648220412945652746650199938239070799 : Nat) • base) + ((330916895653648220412945652746650199938239070799 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep157.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42956781121015365294969681217312514003994247563580404675698060438768365327098 : Int)) * (34915501607149884117459229662462295368919068126477916209019154791746137011211 : Int) =
        (1 : Int) + (57207305313758912731361324688868662932858891950744235330329429267835405971835 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41832893090188087103652368949302522373463407721402170502318733053713670727961 : Int) * ((2 : Int) * (42956781121015365294969681217312514003994247563580404675698060438768365327098 : Int)) =
        (3 : Int) * (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) + (-40964 : Int) * (-40964 : Int) + (8036663442849369319152568307672471616375439812623302486009994944568214724436 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int) =
        (41832893090188087103652368949302522373463407721402170502318733053713670727961 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) - (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) + (-33373924597433683091977249099511202375657468194157304999975757787097070368832 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (16418898027196858049893700505641343202218381678638333858829041735355981185034 : Int) =
        (41832893090188087103652368949302522373463407721402170502318733053713670727961 : Int) * ((32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) - (32497163865107864410659142184213987361103789369805661642600027875981897493121 : Int)) - (42956781121015365294969681217312514003994247563580404675698060438768365327098 : Int) + (-18022962726357105249871363094114122607631081546373095451022348535769538271 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (661833791307296440825891305493300399876478141598 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (661833791307296440825891305493300399876478141598 : Nat) = 330916895653648220412945652746650199938239070799 + 330916895653648220412945652746650199938239070799 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep158
