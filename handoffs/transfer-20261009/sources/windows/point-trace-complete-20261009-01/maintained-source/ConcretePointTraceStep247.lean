import ShielddSecurity.ConcretePointTraceStep246
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep247
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30668999562863422133654530863737643728013407069103903704350978704685986499942
def inputY : F := 29412669514748492492094067424516849589830800333394186345669559416848434687098
def doubleX : F := 17198683190701101891767136889495390095670198304010440389853050069579607737496
def doubleY : F := 40137695433981763480306526138117131065978144588981865135449785692719297149642
def doubleSlope : F := 29696251115639640197110298708707022676961370983567013766525060121307466341590
def addX : F := 36638997471878153231161387444176692100234888765923289061450903936609426886618
def addY : F := 7160036431361236381630122941922975820061908871623977661743934136708218947086
def addSlope : F := 13336210440789524612579023758549156741224775340976927102268099490055975661556
def outX : F := 36638997471878153231161387444176692100234888765923289061450903936609426886618
def outY : F := 7160036431361236381630122941922975820061908871623977661743934136708218947086

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) • base) + ((204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep246.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29412669514748492492094067424516849589830800333394186345669559416848434687098 : Int)) * (20009785309891640312492365229593812147227829710079336974188492031365774421714 : Int) =
        (1 : Int) + (22448035831014265188469901614360482594182527337481567254358781841143087747111 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (29696251115639640197110298708707022676961370983567013766525060121307466341590 : Int) * ((2 : Int) * (29412669514748492492094067424516849589830800333394186345669559416848434687098 : Int)) =
        (3 : Int) * (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) + (-40964 : Int) * (-40964 : Int) + (-20498762711374611387805283922478920756148885161425559127962887365993608817572 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int) =
        (29696251115639640197110298708707022676961370983567013766525060121307466341590 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) - (30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) + (-16818014906356644054893240438713370130550969123045718734264697379145916752776 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (40137695433981763480306526138117131065978144588981865135449785692719297149642 : Int) =
        (29696251115639640197110298708707022676961370983567013766525060121307466341590 : Int) * ((30668999562863422133654530863737643728013407069103903704350978704685986499942 : Int) - (17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int)) - (29412669514748492492094067424516849589830800333394186345669559416848434687098 : Int) + (-7628706420153338141415666329943793252678915322539928881135909013265122114800 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) • base) + ((204827637402836681560342736360101429053310039558509915042667473824755726693 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (35048687303694303472546256350613090104469883825194721533572291479276474302094 : Int) =
        (1 : Int) + (-15026888582368684927477628678576360256357012200411226857133241592140343028283 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (13336210440789524612579023758549156741224775340976927102268099490055975661556 : Int) * ((17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (40137695433981763480306526138117131065978144588981865135449785692719297149642 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-5717810389538977896833405147352349738441335927816947347320871593301608079836 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int) =
        (13336210440789524612579023758549156741224775340976927102268099490055975661556 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-3391847820352423582101220590793741067453014317665736561081167208930517157139 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (7160036431361236381630122941922975820061908871623977661743934136708218947086 : Int) =
        (13336210440789524612579023758549156741224775340976927102268099490055975661556 : Int) * ((17198683190701101891767136889495390095670198304010440389853050069579607737496 : Int) - (36638997471878153231161387444176692100234888765923289061450903936609426886618 : Int)) - (40137695433981763480306526138117131065978144588981865135449785692719297149642 : Int) + (4944327169575827855838416417244942632014001879671987461802019120088721693120 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (409655274805673363120685472720202858106620079117019830085334947649511453387 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (409655274805673363120685472720202858106620079117019830085334947649511453387 : Nat) = 204827637402836681560342736360101429053310039558509915042667473824755726693 + 204827637402836681560342736360101429053310039558509915042667473824755726693 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep247
