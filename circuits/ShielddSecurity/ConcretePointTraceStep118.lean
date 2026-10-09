import ShielddSecurity.ConcretePointTraceStep117
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep118
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 1416164731745743835468194500386466178065195476839366387684349077373560868387
def inputY : F := 2687885643752655296282666548316780698542584926454099869422239096940837501363
def doubleX : F := 11893770990643061008577527254443143771180603174341447628669045791696794618070
def doubleY : F := 27446681108649409716288525877178956956600288735005894891603977269654924881142
def doubleSlope : F := 17813622092208215224435863341232724425743259756505630005153855155055372459470
def outX : F := 11893770990643061008577527254443143771180603174341447628669045791696794618070
def outY : F := 27446681108649409716288525877178956956600288735005894891603977269654924881142

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((300967163324138000837543270560354540 : Nat) • base) + ((300967163324138000837543270560354540 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep117.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (2687885643752655296282666548316780698542584926454099869422239096940837501363 : Int)) * (16609412640261632743001364830316219831070959564040160369308535204665571801781 : Int) =
        (1 : Int) + (1702811353403359669010873923236706515402493577477688702637463839448366297885 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (17813622092208215224435863341232724425743259756505630005153855155055372459470 : Int) * ((2 : Int) * (2687885643752655296282666548316780698542584926454099869422239096940837501363 : Int)) =
        (3 : Int) * (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) + (-40964 : Int) * (-40964 : Int) + (1711526511719478316488556098667572202084458853111365405807960101174657434073 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int) =
        (17813622092208215224435863341232724425743259756505630005153855155055372459470 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) - (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) + (-6051679903962715288451384357172978169727892311703131033467722651134550633648 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27446681108649409716288525877178956956600288735005894891603977269654924881142 : Int) =
        (17813622092208215224435863341232724425743259756505630005153855155055372459470 : Int) * ((1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) - (11893770990643061008577527254443143771180603174341447628669045791696794618070 : Int)) - (2687885643752655296282666548316780698542584926454099869422239096940837501363 : Int) + (3559473694366600150888099832386039911979822012769522910641741856524013087155 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (601934326648276001675086541120709080 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (601934326648276001675086541120709080 : Nat) = 300967163324138000837543270560354540 + 300967163324138000837543270560354540 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep118
