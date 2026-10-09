import ShielddSecurity.ConcretePointTraceStep236
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep237
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 27773554920041364505085995361419327845912299105049653420724124587957958911846
def inputY : F := 3414698383588415840330958276745785235120339748107241774314788446047725028193
def doubleX : F := 17712398429480140543225274045226700555426202639752176633171691637089529533040
def doubleY : F := 28221329087306292075191320043939257391181579682548264477267534273737245139042
def doubleSlope : F := 21041115000334645864629118303398890952745097860757666174917973413644750377297
def outX : F := 17712398429480140543225274045226700555426202639752176633171691637089529533040
def outY : F := 28221329087306292075191320043939257391181579682548264477267534273737245139042

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((200026989651207696836272203476661551809873085506357338908854954906988014 : Nat) • base) + ((200026989651207696836272203476661551809873085506357338908854954906988014 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep236.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3414698383588415840330958276745785235120339748107241774314788446047725028193 : Int)) * (48538590574184473521303739743958104204542527038570466532890877479441281510609 : Int) =
        (1 : Int) + (6321803392115454021792383787928970380329372616035622553019724895073150721121 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (21041115000334645864629118303398890952745097860757666174917973413644750377297 : Int) * ((2 : Int) * (3414698383588415840330958276745785235120339748107241774314788446047725028193 : Int)) =
        (3 : Int) * (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) + (-40964 : Int) * (-40964 : Int) + (-41391755714571365303986629415729695952178116292051488420225047304768847133242 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) =
        (21041115000334645864629118303398890952745097860757666174917973413644750377297 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) - (27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) + (-8443236981907438681767851617776037056220840716309971434744587597173465299565 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (28221329087306292075191320043939257391181579682548264477267534273737245139042 : Int) =
        (21041115000334645864629118303398890952745097860757666174917973413644750377297 : Int) * ((27773554920041364505085995361419327845912299105049653420724124587957958911846 : Int) - (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int)) - (3414698383588415840330958276745785235120339748107241774314788446047725028193 : Int) + (-4037273146433234618005207725378875689043597212589915797293842915287771468819 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) = 200026989651207696836272203476661551809873085506357338908854954906988014 + 200026989651207696836272203476661551809873085506357338908854954906988014 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep237
