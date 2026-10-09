import ShielddSecurity.ConcretePointTraceStep116
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep117
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12403692446580313785633390822410477115426175832151607827485173711655232651623
def inputY : F := 33700085575931962137148683483736065078586451477817979566572420346354213946267
def doubleX : F := 1416164731745743835468194500386466178065195476839366387684349077373560868387
def doubleY : F := 2687885643752655296282666548316780698542584926454099869422239096940837501363
def doubleSlope : F := 22353446105964990815331960644209161069611580310200310888023692162535368984107
def outX : F := 1416164731745743835468194500386466178065195476839366387684349077373560868387
def outY : F := 2687885643752655296282666548316780698542584926454099869422239096940837501363

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((150483581662069000418771635280177270 : Nat) • base) + ((150483581662069000418771635280177270 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep116.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33700085575931962137148683483736065078586451477817979566572420346354213946267 : Int)) * (51236567375409323817219934144799147843924173835025004656216372852834876400941 : Int) =
        (1 : Int) + (65858601554813947657985917654224207638918892583129983950238684236998732878461 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22353446105964990815331960644209161069611580310200310888023692162535368984107 : Int) * ((2 : Int) * (33700085575931962137148683483736065078586451477817979566572420346354213946267 : Int)) =
        (3 : Int) * (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) + (-40964 : Int) * (-40964 : Int) + (19930464228118624545719949436763130383715887941329496555507611551173639580191 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int) =
        (22353446105964990815331960644209161069611580310200310888023692162535368984107 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) - (12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) + (-9529287937761189583824954862826887025001203995359564840421033382144229145168 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2687885643752655296282666548316780698542584926454099869422239096940837501363 : Int) =
        (22353446105964990815331960644209161069611580310200310888023692162535368984107 : Int) * ((12403692446580313785633390822410477115426175832151607827485173711655232651623 : Int) - (1416164731745743835468194500386466178065195476839366387684349077373560868387 : Int)) - (33700085575931962137148683483736065078586451477817979566572420346354213946267 : Int) + (-4683989878896116980302593239863390620476358012069618363531671681570932356894 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (300967163324138000837543270560354540 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (300967163324138000837543270560354540 : Nat) = 150483581662069000418771635280177270 + 150483581662069000418771635280177270 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep117
