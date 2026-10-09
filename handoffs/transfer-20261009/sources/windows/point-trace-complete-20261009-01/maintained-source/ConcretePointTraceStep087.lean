import ShielddSecurity.ConcretePointTraceStep086
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep087
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 42591097252687136101871060178937715056399434788651233410864144025707176688131
def inputY : F := 46275955570477297471008499519235276853342775312990446581249123430270068215578
def doubleX : F := 45774878971391228692067467495918152112664540199492981028025739173355321092830
def doubleY : F := 52035506119804262380316916469875473567529572518009477012579152597609649711911
def doubleSlope : F := 20662072190910897689786498106633160257537093854474151449418029340045934187941
def outX : F := 45774878971391228692067467495918152112664540199492981028025739173355321092830
def outY : F := 52035506119804262380316916469875473567529572518009477012579152597609649711911

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((140148756710876711102921176 : Nat) • base) + ((140148756710876711102921176 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep086.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (46275955570477297471008499519235276853342775312990446581249123430270068215578 : Int)) * (37521907073302169137603424392272617172799480216743156481506265736623300517584 : Int) =
        (1 : Int) + (66228020371342275426343053690536989411106592983951679296064146229035999994431 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (20662072190910897689786498106633160257537093854474151449418029340045934187941 : Int) * ((2 : Int) * (46275955570477297471008499519235276853342775312990446581249123430270068215578 : Int)) =
        (3 : Int) * (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) + (-40964 : Int) * (-40964 : Int) + (-67314418122590098846574639544261513899178446247345615300774333010588038871159 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) =
        (20662072190910897689786498106633160257537093854474151449418029340045934187941 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) - (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) + (-8141777471942157756619044362196782519101285630063268336659769895809855249789 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (52035506119804262380316916469875473567529572518009477012579152597609649711911 : Int) =
        (20662072190910897689786498106633160257537093854474151449418029340045934187941 : Int) * ((42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) - (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int)) - (46275955570477297471008499519235276853342775312990446581249123430270068215578 : Int) + (1254551916836735075082239992275080517187111727440756466833039674839841173096 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (280297513421753422205842352 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (280297513421753422205842352 : Nat) = 140148756710876711102921176 + 140148756710876711102921176 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep087
