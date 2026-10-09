import ShielddSecurity.ConcretePointTraceStep145
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep146
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3217164406942250688713204317082327471730732295092474899332778098584295944176
def inputY : F := 1064446204116300190898886914470289042670945552971969977294460935733908085470
def doubleX : F := 39651586123580376443048613161615770209033490101544976781278983951114780125655
def doubleY : F := 29990184430001635833391747276110256695705902600559755346520651178972125854927
def doubleSlope : F := 47499285713189202172696904210902305508503119376872423314886797253588980670244
def outX : F := 39651586123580376443048613161615770209033490101544976781278983951114780125655
def outY : F := 29990184430001635833391747276110256695705902600559755346520651178972125854927

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((80790257727941460061754309752600146469296648 : Nat) • base) + ((80790257727941460061754309752600146469296648 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep145.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1064446204116300190898886914470289042670945552971969977294460935733908085470 : Int)) * (31410755847180977501408022378726738056544787819338927710941762306752792973075 : Int) =
        (1 : Int) + (1275274217061838475217152222565847506874271345039800524647522804374765895923 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (47499285713189202172696904210902305508503119376872423314886797253588980670244 : Int) * ((2 : Int) * (1064446204116300190898886914470289042670945552971969977294460935733908085470 : Int)) =
        (3 : Int) * (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) + (-40964 : Int) * (-40964 : Int) + (1336307023643051647928022712539600480501379361639119826464125460675559771744 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int) =
        (47499285713189202172696904210902305508503119376872423314886797253588980670244 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) - (3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) + (-43027452783575099346852136915750803872894057739515893424915199845583494345569 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29990184430001635833391747276110256695705902600559755346520651178972125854927 : Int) =
        (47499285713189202172696904210902305508503119376872423314886797253588980670244 : Int) * ((3217164406942250688713204317082327471730732295092474899332778098584295944176 : Int) - (39651586123580376443048613161615770209033490101544976781278983951114780125655 : Int)) - (1064446204116300190898886914470289042670945552971969977294460935733908085470 : Int) + (33004293360862263994446686546751458118575736793361947135458903791567327540521 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (161580515455882920123508619505200292938593296 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (161580515455882920123508619505200292938593296 : Nat) = 80790257727941460061754309752600146469296648 + 80790257727941460061754309752600146469296648 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep146
