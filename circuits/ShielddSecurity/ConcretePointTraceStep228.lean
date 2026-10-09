import ShielddSecurity.ConcretePointTraceStep227
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep228
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 24188445313190595005135390897078619891378705797914974064515670624335802659725
def inputY : F := 14638837250991371995610211486798395067626841606728948335074620493566100466149
def doubleX : F := 13798753265288654467340715281747526995117396230873746677503606389997596797510
def doubleY : F := 36793796833757024920901569456538656721335438875908648744202901923515408471070
def doubleSlope : F := 15490351255414705009329229181126706932457400056754177809180960300499997480170
def addX : F := 15441869308184954090525659289032805624825465995953187764959659042862426772171
def addY : F := 26731209053065475463851289180978038803496826261633296358843280569828481262485
def addSlope : F := 20730555204242826792500304782956349173724933886077940415357261656363535840737
def outX : F := 15441869308184954090525659289032805624825465995953187764959659042862426772171
def outY : F := 26731209053065475463851289180978038803496826261633296358843280569828481262485

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((390677714162515032883344147415354593378658370129604177556357333802710 : Nat) • base) + ((390677714162515032883344147415354593378658370129604177556357333802710 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep227.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (14638837250991371995610211486798395067626841606728948335074620493566100466149 : Int)) * (37045577081655084429363916428078871418619374115084654831716632590101220287591 : Int) =
        (1 : Int) + (20684471154766021223764894193831263563881874967175094623239582667988617469509 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15490351255414705009329229181126706932457400056754177809180960300499997480170 : Int) * ((2 : Int) * (14638837250991371995610211486798395067626841606728948335074620493566100466149 : Int)) =
        (3 : Int) * (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) + (-40964 : Int) * (-40964 : Int) + (-24825011381667894671889071922996156132993037974382736257333920350044238666647 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int) =
        (15490351255414705009329229181126706932457400056754177809180960300499997480170 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) - (24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) + (-4576084240317067794307654444002701065063860950632511270703337326330384536716 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36793796833757024920901569456538656721335438875908648744202901923515408471070 : Int) =
        (15490351255414705009329229181126706932457400056754177809180960300499997480170 : Int) * ((24188445313190595005135390897078619891378705797914974064515670624335802659725 : Int) - (13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int)) - (14638837250991371995610211486798395067626841606728948335074620493566100466149 : Int) + (-3069272301074026826729471472726822414809272903081601759692147227435470325987 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((390677714162515032883344147415354593378658370129604177556357333802710 : Nat) • base) + ((390677714162515032883344147415354593378658370129604177556357333802710 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (42056433540329105873909061373105070740210310768790942182201630970031243567993 : Int) =
        (1 : Int) + (-20758341923813241811690952622642496784024313345234236088757020569024405472230 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (20730555204242826792500304782956349173724933886077940415357261656363535840737 : Int) * ((13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (36793796833757024920901569456538656721335438875908648744202901923515408471070 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-10232250264100524570662903015727167608212744950756989448318871406442791905825 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) =
        (20730555204242826792500304782956349173724933886077940415357261656363535840737 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-8195837632934580144338341511815949567634457225754073374178679318908085210021 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (26731209053065475463851289180978038803496826261633296358843280569828481262485 : Int) =
        (20730555204242826792500304782956349173724933886077940415357261656363535840737 : Int) * ((13798753265288654467340715281747526995117396230873746677503606389997596797510 : Int) - (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int)) - (36793796833757024920901569456538656721335438875908648744202901923515408471070 : Int) + (649606928853110150732935363065617349633784237696760281072494230137065020824 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (781355428325030065766688294830709186757316740259208355112714667605421 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (781355428325030065766688294830709186757316740259208355112714667605421 : Nat) = 390677714162515032883344147415354593378658370129604177556357333802710 + 390677714162515032883344147415354593378658370129604177556357333802710 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep228
