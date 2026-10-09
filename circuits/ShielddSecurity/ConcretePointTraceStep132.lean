import ShielddSecurity.ConcretePointTraceStep131
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep132
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39691555183271552178319106048561723403130251332419267418136347793447725612754
def inputY : F := 37227449205795891773235904093255107020145147318615181278104111621123678735905
def doubleX : F := 8750949743486244879832974919727339812249473397508506460414106552978630048253
def doubleY : F := 29983144448755360265655030035249929695952211445658121200202837882361415553500
def doubleSlope : F := 16314361457312842816892091891641363383987152505120288410714166066423712267768
def outX : F := 8750949743486244879832974919727339812249473397508506460414106552978630048253
def outY : F := 29983144448755360265655030035249929695952211445658121200202837882361415553500

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4931046003902677005722308944860848783526 : Nat) • base) + ((4931046003902677005722308944860848783526 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep131.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37227449205795891773235904093255107020145147318615181278104111621123678735905 : Int)) * (6882529161481304379074968918101600850093994279615106797864565798911771070144 : Int) =
        (1 : Int) + (9772660565337370334325755666263306193332313984601590638176571448393254456703 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16314361457312842816892091891641363383987152505120288410714166066423712267768 : Int) * ((2 : Int) * (37227449205795891773235904093255107020145147318615181278104111621123678735905 : Int)) =
        (3 : Int) * (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) + (-40964 : Int) * (-40964 : Int) + (-66968931517169159613572203931864951968933136789526877021056538396616712136140 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int) =
        (16314361457312842816892091891641363383987152505120288410714166066423712267768 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) - (39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) + (-5075883426584083828517575421611428676592324943480411303756101114764444395687 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29983144448755360265655030035249929695952211445658121200202837882361415553500 : Int) =
        (16314361457312842816892091891641363383987152505120288410714166066423712267768 : Int) * ((39691555183271552178319106048561723403130251332419267418136347793447725612754 : Int) - (8750949743486244879832974919727339812249473397508506460414106552978630048253 : Int)) - (37227449205795891773235904093255107020145147318615181278104111621123678735905 : Int) + (-9626543261972793415816185749110931687172245896183547541845257612868375023451 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (9862092007805354011444617889721697567052 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (9862092007805354011444617889721697567052 : Nat) = 4931046003902677005722308944860848783526 + 4931046003902677005722308944860848783526 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep132
