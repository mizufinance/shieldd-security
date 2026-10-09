import ShielddSecurity.ConcretePointTraceStep101
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep102
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 216336399648223157118731964782775655145726175811068750054785231901207849557
def inputY : F := 38721984196570982431023641772955493920986040998650679425521324927636306039705
def doubleX : F := 6451728148494273952772804252983850502619998973624730481120785746494157718451
def doubleY : F := 37509554204313012901739290583800469639097394563092267985999778135697776991124
def doubleSlope : F := 50732068723361192870723137631864233409797874183623283074581861210391394574110
def addX : F := 4135579946183550342138252281696287041372198289593503635539368313089709755681
def addY : F := 46716454846539337129234035002814852559935032755158051812237089092077353354247
def addSlope : F := 12083000011959713612257169264591810833274466548261806354669463301576521347440
def outX : F := 4135579946183550342138252281696287041372198289593503635539368313089709755681
def outY : F := 46716454846539337129234035002814852559935032755158051812237089092077353354247

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4592394459902008069420521096196 : Nat) • base) + ((4592394459902008069420521096196 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep101.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (38721984196570982431023641772955493920986040998650679425521324927636306039705 : Int)) * (22313333122168780457639981492596169007165378211285275429470395782203723630776 : Int) =
        (1 : Int) + (32955167798526748289494030481141468627121957599751675312962392278365513333743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (50732068723361192870723137631864233409797874183623283074581861210391394574110 : Int) * ((2 : Int) * (38721984196570982431023641772955493920986040998650679425521324927636306039705 : Int)) =
        (3 : Int) * (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) + (-40964 : Int) * (-40964 : Int) + (74924892724607741368162234824516791542432447386980902997891591587330886126193 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int) =
        (50732068723361192870723137631864233409797874183623283074581861210391394574110 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) - (216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) + (-49083624300271805041446304811971154541195670804728569844192514713661744394031 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (37509554204313012901739290583800469639097394563092267985999778135697776991124 : Int) =
        (50732068723361192870723137631864233409797874183623283074581861210391394574110 : Int) * ((216336399648223157118731964782775655145726175811068750054785231901207849557 : Int) - (6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int)) - (38721984196570982431023641772955493920986040998650679425521324927636306039705 : Int) + (6032784265792049002817377156266414030244140034093791278947417403088937470513 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((4592394459902008069420521096196 : Nat) • base) + ((4592394459902008069420521096196 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (33592324211940075922268235652231985025881885107902704021932050583903046112979 : Int) =
        (1 : Int) + (-21287372058107442772492986620750722081686052472017809087379417614764761753633 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (12083000011959713612257169264591810833274466548261806354669463301576521347440 : Int) * ((6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (37509554204313012901739290583800469639097394563092267985999778135697776991124 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-7656966966914374369883751296448555284881397408674542429873264833246714063466 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) =
        (12083000011959713612257169264591810833274466548261806354669463301576521347440 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-2784332078017368251105475456686487042720710889086330238718835432822094600481 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (46716454846539337129234035002814852559935032755158051812237089092077353354247 : Int) =
        (12083000011959713612257169264591810833274466548261806354669463301576521347440 : Int) * ((6451728148494273952772804252983850502619998973624730481120785746494157718451 : Int) - (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int)) - (37509554204313012901739290583800469639097394563092267985999778135697776991124 : Int) + (-533718921687733465466274034835176399709569977591697047255643732111545086533 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (9184788919804016138841042192393 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (9184788919804016138841042192393 : Nat) = 4592394459902008069420521096196 + 4592394459902008069420521096196 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep102
