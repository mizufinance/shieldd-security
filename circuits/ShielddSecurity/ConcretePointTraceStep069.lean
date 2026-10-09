import ShielddSecurity.ConcretePointTraceStep068
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep069
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10721626244760493793223850252016159894508010638733582775465440128313675940066
def inputY : F := 52407775636179615762342089679217248497425522703220290175166220734132236976569
def doubleX : F := 28184953543859809640812727532633588788793437427981301895063536319444627338427
def doubleY : F := 8869901820034805539351570749968161108337273747837906015282708030448050702499
def doubleSlope : F := 4525447311783802247823283230658773736588210239387472471866584799427414123736
def addX : F := 41167131855506120034763848086695538957685888449975927237808442306593912360816
def addY : F := 39344158252348397193155435181087501524005516557562691279107444282911777716185
def addSlope : F := 19775796626319062056579851565392225638256446176803117979147305410065236568728
def outX : F := 41167131855506120034763848086695538957685888449975927237808442306593912360816
def outY : F := 39344158252348397193155435181087501524005516557562691279107444282911777716185

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((534625079005724758540 : Nat) • base) + ((534625079005724758540 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep068.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (52407775636179615762342089679217248497425522703220290175166220734132236976569 : Int)) * (40604580908551779561932704200209087888924996398255038938126598399231341417994 : Int) =
        (1 : Int) + (81165643138380697543630228218417086380944244444203321066953235944094531415667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (4525447311783802247823283230658773736588210239387472471866584799427414123736 : Int) * ((2 : Int) * (52407775636179615762342089679217248497425522703220290175166220734132236976569 : Int)) =
        (3 : Int) * (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) + (-40964 : Int) * (-40964 : Int) + (2469253088828849846915144529993322606684775256423452469786928753032930011060 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int) =
        (4525447311783802247823283230658773736588210239387472471866584799427414123736 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) - (10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) + (-390566063850996963021438446376518476120007031825318164154331875950623293385 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (8869901820034805539351570749968161108337273747837906015282708030448050702499 : Int) =
        (4525447311783802247823283230658773736588210239387472471866584799427414123736 : Int) * ((10721626244760493793223850252016159894508010638733582775465440128313675940066 : Int) - (28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int)) - (52407775636179615762342089679217248497425522703220290175166220734132236976569 : Int) + (1507162173160381456314310726869860725921350304667482837566740190095611923828 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((534625079005724758540 : Nat) • base) + ((534625079005724758540 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (791270759284072507685833125911433238663029421665804592797961900549212734485 : Int) =
        (1 : Int) + (-173466380012985591604207665555330631708213777464255253005800160761387843897 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (19775796626319062056579851565392225638256446176803117979147305410065236568728 : Int) * ((28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (8869901820034805539351570749968161108337273747837906015282708030448050702499 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4335350210267313862233305838378165182929592771548064847814362039538119807417 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) =
        (19775796626319062056579851565392225638256446176803117979147305410065236568728 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-7458293218133385164063615089903876808576275568623064922794483232183803957002 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (39344158252348397193155435181087501524005516557562691279107444282911777716185 : Int) =
        (19775796626319062056579851565392225638256446176803117979147305410065236568728 : Int) * ((28184953543859809640812727532633588788793437427981301895063536319444627338427 : Int) - (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int)) - (8869901820034805539351570749968161108337273747837906015282708030448050702499 : Int) + (4896131078203363981077103333385367713106535773215277775529884501644145790452 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1069250158011449517081 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1069250158011449517081 : Nat) = 534625079005724758540 + 534625079005724758540 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep069
