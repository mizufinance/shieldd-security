import ShielddSecurity.ConcretePointTraceStep130
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep131
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31064732792922849611614979585316239990262623870026372100056844447085781120353
def inputY : F := 7890566641986631886466338004070462272929878721315277994735447770683241547753
def doubleX : F := 39691555183271552178319106048561723403130251332419267418136347793447725612754
def doubleY : F := 37227449205795891773235904093255107020145147318615181278104111621123678735905
def doubleSlope : F := 35635351408411228549685830544244109063549504530219824872676613293108424484974
def outX : F := 39691555183271552178319106048561723403130251332419267418136347793447725612754
def outY : F := 37227449205795891773235904093255107020145147318615181278104111621123678735905

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2465523001951338502861154472430424391763 : Nat) • base) + ((2465523001951338502861154472430424391763 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep130.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7890566641986631886466338004070462272929878721315277994735447770683241547753 : Int)) * (45188530418782572101447439698107939627833675480565021932314033766999648029944 : Int) =
        (1 : Int) + (13599967943015680772681290848916851765005251534154711541444911284844434205551 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (35635351408411228549685830544244109063549504530219824872676613293108424484974 : Int) * ((2 : Int) * (7890566641986631886466338004070462272929878721315277994735447770683241547753 : Int)) =
        (3 : Int) * (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) + (-40964 : Int) * (-40964 : Int) + (-44486463370716746611964846305533316470855073765262778130981906969608784181767 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) =
        (35635351408411228549685830544244109063549504530219824872676613293108424484974 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) - (31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) + (-24217737679781180123867960784811261270824372627346165347660143654530992022968 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (37227449205795891773235904093255107020145147318615181278104111621123678735905 : Int) =
        (35635351408411228549685830544244109063549504530219824872676613293108424484974 : Int) * ((31064732792922849611614979585316239990262623870026372100056844447085781120353 : Int) - (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int)) - (7890566641986631886466338004070462272929878721315277994735447770683241547753 : Int) + (5862777085178808262926633098389714497283397915834669331711408624048565619864 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4931046003902677005722308944860848783526 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4931046003902677005722308944860848783526 : Nat) = 2465523001951338502861154472430424391763 + 2465523001951338502861154472430424391763 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep131
