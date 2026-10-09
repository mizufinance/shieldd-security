import ShielddSecurity.ConcretePointTraceStep199
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep200
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 23583482757384776112905908020534842931740118371752496005305901943570318379491
def inputY : F := 8629374278687061807636190405225030541556281048258008138682302097311798496146
def doubleX : F := 27917619233653858553474252533019435221491774704687086999359922332967845712847
def doubleY : F := 17240713838745046324314945059024113113341998238135875130352949585740987791529
def doubleSlope : F := 41635137628020841560062227075329057211793845437362686080755186710570365621961
def outX : F := 27917619233653858553474252533019435221491774704687086999359922332967845712847
def outY : F := 17240713838745046324314945059024113113341998238135875130352949585740987791529

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1455387898394893977356494022217968826661476381605879133777161 : Nat) • base) + ((1455387898394893977356494022217968826661476381605879133777161 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep199.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8629374278687061807636190405225030541556281048258008138682302097311798496146 : Int)) * (6966335515155673464303227288002004275786350259641047219127951953319942480491 : Int) =
        (1 : Int) + (2292900282885147048077543646702305199959676208071096826647886526632739501067 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41635137628020841560062227075329057211793845437362686080755186710570365621961 : Int) * ((2 : Int) * (8629374278687061807636190405225030541556281048258008138682302097311798496146 : Int)) =
        (3 : Int) * (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) + (-40964 : Int) * (-40964 : Int) + (-18116825594255587189812892551470719918637782185945101274464265819015677303927 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) =
        (41635137628020841560062227075329057211793845437362686080755186710570365621961 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) - (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) + (-33059135172526758550656682658057530693017133857421096023446873180327314391620 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (17240713838745046324314945059024113113341998238135875130352949585740987791529 : Int) =
        (41635137628020841560062227075329057211793845437362686080755186710570365621961 : Int) * ((23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) - (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int)) - (8629374278687061807636190405225030541556281048258008138682302097311798496146 : Int) + (3441391377285317956212833464842527040807251049331936757212772136426347894407 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2910775796789787954712988044435937653322952763211758267554322 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (2910775796789787954712988044435937653322952763211758267554322 : Nat) = 1455387898394893977356494022217968826661476381605879133777161 + 1455387898394893977356494022217968826661476381605879133777161 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep200
