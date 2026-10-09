import ShielddSecurity.ConcretePointTraceStep045
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep046
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32510813837869581354012590503628603748655675077490635625567946577528389800880
def inputY : F := 44037891352928711476637246091610747034246896357656061059278012919965223845366
def doubleX : F := 48892350805995233437257946463586114587302588009948186414316788738496184429201
def doubleY : F := 858304328011277787528787548709820867821380479700566703099030347686643327037
def doubleSlope : F := 5944672959107404329118426806900050917633317882715984305864110259776519710886
def addX : F := 49247472984684596498223657552728494939904532011843055046126173280548413673307
def addY : F := 11438903628521316103570136825836017673458105972056446291778971950032122130410
def addSlope : F := 8786255157682034470651323551585917423597902406813734742043984970564585060930
def outX : F := 49247472984684596498223657552728494939904532011843055046126173280548413673307
def outY : F := 11438903628521316103570136825836017673458105972056446291778971950032122130410

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((63732275844302 : Nat) • base) + ((63732275844302 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep045.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (44037891352928711476637246091610747034246896357656061059278012919965223845366 : Int)) * (38196699203156679019811880635961825912685417783435121971253771059968676466455 : Int) =
        (1 : Int) + (64158444344876500923243920845850482410896062705984429524963342237906574997043 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (5944672959107404329118426806900050917633317882715984305864110259776519710886 : Int) * ((2 : Int) * (44037891352928711476637246091610747034246896357656061059278012919965223845366 : Int)) =
        (3 : Int) * (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) + (-40964 : Int) * (-40964 : Int) + (-50485994875773249214510075286531647555753211200410229062682413844941665752328 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int) =
        (5944672959107404329118426806900050917633317882715984305864110259776519710886 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) - (32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) + (-673949590289406986732323638322542269648514429459674337252154675191366105531 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (858304328011277787528787548709820867821380479700566703099030347686643327037 : Int) =
        (5944672959107404329118426806900050917633317882715984305864110259776519710886 : Int) * ((32510813837869581354012590503628603748655675077490635625567946577528389800880 : Int) - (48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int)) - (44037891352928711476637246091610747034246896357656061059278012919965223845366 : Int) + (1857180404022893251078388821384211911451667404173722196856586760127390112793 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((63732275844302 : Nat) • base) + ((63732275844302 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (1252300409226674446136877529186567349729899189443864821866966639845284379555 : Int) =
        (1 : Int) + (220009027220110459115576186346479530885050101947327267221452553091548644153 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (8786255157682034470651323551585917423597902406813734742043984970564585060930 : Int) * ((48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (858304328011277787528787548709820867821380479700566703099030347686643327037 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1543603624104068418765311600522637690057403045152598997802292797149994048873 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) =
        (8786255157682034470651323551585917423597902406813734742043984970564585060930 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1472241655890477268820932379944380336178546107102190024306751600056424175629 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (11438903628521316103570136825836017673458105972056446291778971950032122130410 : Int) =
        (8786255157682034470651323551585917423597902406813734742043984970564585060930 : Int) * ((48892350805995233437257946463586114587302588009948186414316788738496184429201 : Int) - (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int)) - (858304328011277787528787548709820867821380479700566703099030347686643327037 : Int) + (59504948924678423746360412386478369179869108183313776534239114579018731579 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (127464551688605 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (127464551688605 : Nat) = 63732275844302 + 63732275844302 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep046
