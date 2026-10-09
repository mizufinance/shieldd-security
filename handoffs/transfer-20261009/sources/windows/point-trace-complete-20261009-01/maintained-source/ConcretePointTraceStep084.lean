import ShielddSecurity.ConcretePointTraceStep083
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep084
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41563599201413627549918984709942676221534178397299148638277086857557536743764
def inputY : F := 28078021518674186043865099631687949879699115245450967847538986726666947435736
def doubleX : F := 10980352158563505595411202311065466247344052636350715621156904004400508454
def doubleY : F := 50884997764072393255343512754124160141563849760913156726834962519552580102715
def doubleSlope : F := 41679220459962514319718833710178336326942156549200617141935106523548471663378
def outX : F := 10980352158563505595411202311065466247344052636350715621156904004400508454
def outY : F := 50884997764072393255343512754124160141563849760913156726834962519552580102715

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((17518594588859588887865147 : Nat) • base) + ((17518594588859588887865147 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep083.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28078021518674186043865099631687949879699115245450967847538986726666947435736 : Int)) * (48090800093806929899761143687567736550793247281112323530118583937798912255465 : Int) =
        (1 : Int) + (51502697928638890785990528098350992364946342326516805359944921950586576302383 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41679220459962514319718833710178336326942156549200617141935106523548471663378 : Int) * ((2 : Int) * (28078021518674186043865099631687949879699115245450967847538986726666947435736 : Int)) =
        (3 : Int) * (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) + (-40964 : Int) * (-40964 : Int) + (-54200644660216243668253903256451915694834695184985027529553427050922650212128 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int) =
        (41679220459962514319718833710178336326942156549200617141935106523548471663378 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) - (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) + (-33129177540154926515678897111467845729643362782230222037451895481230754929790 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (50884997764072393255343512754124160141563849760913156726834962519552580102715 : Int) =
        (41679220459962514319718833710178336326942156549200617141935106523548471663378 : Int) * ((41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) - (10980352158563505595411202311065466247344052636350715621156904004400508454 : Int)) - (28078021518674186043865099631687949879699115245450967847538986726666947435736 : Int) + (-33028546885557494744776183012285592168706898056230281250484931298825405934633 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (35037189177719177775730294 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (35037189177719177775730294 : Nat) = 17518594588859588887865147 + 17518594588859588887865147 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep084
