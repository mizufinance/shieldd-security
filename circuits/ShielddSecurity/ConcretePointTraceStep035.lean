import ShielddSecurity.ConcretePointTraceStep034
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep035
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45466447067294891010862106179202775952771623178765382482196860805216651862813
def inputY : F := 18625121304602990171159681503757143764427980449603755414902894215780626446621
def doubleX : F := 46781058235981457002749766384951815955172701253831443920486925736518244670534
def doubleY : F := 13874074668900920225514555802496495702156842640960959213813645035710780847980
def doubleSlope : F := 20980812002773924237502455525181391967859618700286710881706415128784173414674
def addX : F := 22609393211005250822101538537476652589974078742650691228624105849553002896316
def addY : F := 49884585325894152805550737203374553372729977618737100674497782470942008989896
def addSlope : F := 49239768485086231070157545003295539031684361159622624347896537721623356237993
def outX : F := 22609393211005250822101538537476652589974078742650691228624105849553002896316
def outY : F := 49884585325894152805550737203374553372729977618737100674497782470942008989896

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((31119275314 : Nat) • base) + ((31119275314 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep034.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18625121304602990171159681503757143764427980449603755414902894215780626446621 : Int)) * (14740019148503812732514738453649283233413862325034329630778257229307829059146 : Int) =
        (1 : Int) + (10471252506272055474727664559180817228822168976882034674635015083350400929987 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (20980812002773924237502455525181391967859618700286710881706415128784173414674 : Int) * ((2 : Int) * (18625121304602990171159681503757143764427980449603755414902894215780626446621 : Int)) =
        (3 : Int) * (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) + (-40964 : Int) * (-40964 : Int) + (-103365359525819554870075927920121807626142073631096794863433535246869935337479 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int) =
        (20980812002773924237502455525181391967859618700286710881706415128784173414674 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) - (45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) + (-8394910370534938022071084479597765580655327617760435395394693393673439896268 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (13874074668900920225514555802496495702156842640960959213813645035710780847980 : Int) =
        (20980812002773924237502455525181391967859618700286710881706415128784173414674 : Int) * ((45466447067294891010862106179202775952771623178765382482196860805216651862813 : Int) - (46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int)) - (18625121304602990171159681503757143764427980449603755414902894215780626446621 : Int) + (526006473522988791728756288926889484297109259492459398645307039997054064235 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((31119275314 : Nat) • base) + ((31119275314 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (18230123797043186717658130219770525703097693812616561248569603799756848344417 : Int) =
        (1 : Int) + (2468716610310953158000751065059325870139955032297740449241564925352327520082 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (49239768485086231070157545003295539031684361159622624347896537721623356237993 : Int) * ((46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (13874074668900920225514555802496495702156842640960959213813645035710780847980 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (6668031204851955019001886876714310058126606372862279806926132200596288793193 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int) =
        (49239768485086231070157545003295539031684361159622624347896537721623356237993 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-46238473037158692488726246859183384344854497986243361328696645719155434971268 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (49884585325894152805550737203374553372729977618737100674497782470942008989896 : Int) =
        (49239768485086231070157545003295539031684361159622624347896537721623356237993 : Int) * ((46781058235981457002749766384951815955172701253831443920486925736518244670534 : Int) - (22609393211005250822101538537476652589974078742650691228624105849553002896316 : Int)) - (13874074668900920225514555802496495702156842640960959213813645035710780847980 : Int) + (-22698337459874773024127560400302436195393065328275388993819262605543823203046 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (62238550629 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (62238550629 : Nat) = 31119275314 + 31119275314 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep035
