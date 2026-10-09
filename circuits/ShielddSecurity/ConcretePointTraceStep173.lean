import ShielddSecurity.ConcretePointTraceStep172
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep173
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4384458270312404527472311720528415181244761365469771907195408673353958364732
def inputY : F := 40818718863369315974009069930431336203247929834174035758463127960833108865186
def doubleX : F := 8382594515793085882721201356307248973461400156430952611421509330385906310
def doubleY : F := 7153271406608474228879463644272109681016934945510705844143638590377569135739
def doubleSlope : F := 52321919780063927966236034513791954317347476996040548762182924525971232761633
def outX : F := 8382594515793085882721201356307248973461400156430952611421509330385906310
def outY : F := 7153271406608474228879463644272109681016934945510705844143638590377569135739

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((10843484836778744886491403149202233751576217871948176 : Nat) • base) + ((10843484836778744886491403149202233751576217871948176 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep172.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (40818718863369315974009069930431336203247929834174035758463127960833108865186 : Int)) * (22217575155478372426757949098948269942303778005993046448880583350493709394587 : Int) =
        (1 : Int) + (34590552787319545470064212620591235172203123970760127823313838216316094737451 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (52321919780063927966236034513791954317347476996040548762182924525971232761633 : Int) * ((2 : Int) * (40818718863369315974009069930431336203247929834174035758463127960833108865186 : Int)) =
        (3 : Int) * (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) + (-40964 : Int) * (-40964 : Int) + (80360192916450353868179534295918641291970132237580895045591338611505016516420 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) =
        (52321919780063927966236034513791954317347476996040548762182924525971232761633 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) - (4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) + (-52208212036671832605379754949912002804144635542241184121948344453682867305291 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (7153271406608474228879463644272109681016934945510705844143638590377569135739 : Int) =
        (52321919780063927966236034513791954317347476996040548762182924525971232761633 : Int) * ((4384458270312404527472311720528415181244761365469771907195408673353958364732 : Int) - (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int)) - (40818718863369315974009069930431336203247929834174035758463127960833108865186 : Int) + (-4366565441995949790573204915915075296753389324384371537634633400238264581977 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (21686969673557489772982806298404467503152435743896352 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (21686969673557489772982806298404467503152435743896352 : Nat) = 10843484836778744886491403149202233751576217871948176 + 10843484836778744886491403149202233751576217871948176 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep173
