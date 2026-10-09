import ShielddSecurity.ConcretePointTraceStep228
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep229
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15441869308184954090525659289032805624825465995953187764959659042862426772171
def inputY : F := 26731209053065475463851289180978038803496826261633296358843280569828481262485
def doubleX : F := 39276990320207231158320426183016590690332878618784652145260184713194201429828
def doubleY : F := 25827448544319665073548703524385993454323684979965369498133895144861502025203
def doubleSlope : F := 15660121002258651955327549258105377056607994680652486231140485499826011605444
def addX : F := 40626827023203268955061382922832853403565936910713743647620890213540648366764
def addY : F := 44639586313569380652127228493501711701688349631168306188810122534468419439433
def addSlope : F := 15941158004440265721127934111318263083687277591973069397941997159796755688064
def outX : F := 40626827023203268955061382922832853403565936910713743647620890213540648366764
def outY : F := 44639586313569380652127228493501711701688349631168306188810122534468419439433

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((781355428325030065766688294830709186757316740259208355112714667605421 : Nat) • base) + ((781355428325030065766688294830709186757316740259208355112714667605421 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep228.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (26731209053065475463851289180978038803496826261633296358843280569828481262485 : Int)) * (3439819660128804774097680786457463227429870788610153151937830415640196707130 : Int) =
        (1 : Int) + (3507161390275257398622089175060041671296524692473680314145867300972480757123 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15660121002258651955327549258105377056607994680652486231140485499826011605444 : Int) * ((2 : Int) * (26731209053065475463851289180978038803496826261633296358843280569828481262485 : Int)) =
        (3 : Int) * (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) + (-40964 : Int) * (-40964 : Int) + (2324247531201195645899749276647238047853071088327074798162850826841959865309 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int) =
        (15660121002258651955327549258105377056607994680652486231140485499826011605444 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) - (15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) + (-4676939003808518786002985900003711079127216953372265419389046878889922150718 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25827448544319665073548703524385993454323684979965369498133895144861502025203 : Int) =
        (15660121002258651955327549258105377056607994680652486231140485499826011605444 : Int) * ((15441869308184954090525659289032805624825465995953187764959659042862426772171 : Int) - (39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int)) - (26731209053065475463851289180978038803496826261633296358843280569828481262485 : Int) + (7118425656196712439252151064186416033564950699746968913666188025406365384492 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((781355428325030065766688294830709186757316740259208355112714667605421 : Nat) • base) + ((781355428325030065766688294830709186757316740259208355112714667605421 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (19656783592954233134764596829679118033221955066536156692162983338408954854836 : Int) =
        (1 : Int) + (-151156634830809553612161237564056656586198329715330231864648104394209079437 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (15941158004440265721127934111318263083687277591973069397941997159796755688064 : Int) * ((39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (25827448544319665073548703524385993454323684979965369498133895144861502025203 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-122584236015149189235463929518492953408066549431263363860198559987894419529 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int) =
        (15941158004440265721127934111318263083687277591973069397941997159796755688064 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4846310234621127340659958758637002680425514918803830666045664727829922197253 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (44639586313569380652127228493501711701688349631168306188810122534468419439433 : Int) =
        (15941158004440265721127934111318263083687277591973069397941997159796755688064 : Int) * ((39276990320207231158320426183016590690332878618784652145260184713194201429828 : Int) - (40626827023203268955061382922832853403565936910713743647620890213540648366764 : Int)) - (25827448544319665073548703524385993454323684979965369498133895144861502025203 : Int) + (410367140641526655076487500226007514797326580448095003936301461031516683580 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1562710856650060131533376589661418373514633480518416710225429335210843 : Nat) = 781355428325030065766688294830709186757316740259208355112714667605421 + 781355428325030065766688294830709186757316740259208355112714667605421 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep229
