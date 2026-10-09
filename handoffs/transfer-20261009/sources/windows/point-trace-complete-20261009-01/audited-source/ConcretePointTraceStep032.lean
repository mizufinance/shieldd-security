import ShielddSecurity.ConcretePointTraceStep031
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep032
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25680312995057712136325629919018021145739081556782014044361090614908200595667
def inputY : F := 16064879780612197845009179244966897833355462192413675642089857015121101354157
def doubleX : F := 38181194461775874478356199072964542949872183977958664827468175589256533116719
def doubleY : F := 38499690297543201976920611390853219381284318318842412359424883691023049216125
def doubleSlope : F := 16990379539080822787903169698054101968062628549070765811630625167141974192093
def outX : F := 38181194461775874478356199072964542949872183977958664827468175589256533116719
def outY : F := 38499690297543201976920611390853219381284318318842412359424883691023049216125

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3889909414 : Nat) • base) + ((3889909414 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep031.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16064879780612197845009179244966897833355462192413675642089857015121101354157 : Int)) * (14423639647712261347789599127382081431237347260926202503170797503083526203683 : Int) =
        (1 : Int) + (8837996358999895959865584202409387065812455565591210733491441267330835697997 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16990379539080822787903169698054101968062628549070765811630625167141974192093 : Int) * ((2 : Int) * (16064879780612197845009179244966897833355462192413675642089857015121101354157 : Int)) =
        (3 : Int) * (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) + (-40964 : Int) * (-40964 : Int) + (-27319818966372941753922146618241820384219461386013080765810360474266212688873 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) =
        (16990379539080822787903169698054101968062628549070765811630625167141974192093 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) - (25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) + (-5505257534424694783727410087893619136046690499031485653769774961867140447228 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (38499690297543201976920611390853219381284318318842412359424883691023049216125 : Int) =
        (16990379539080822787903169698054101968062628549070765811630625167141974192093 : Int) * ((25680312995057712136325629919018021145739081556782014044361090614908200595667 : Int) - (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int)) - (16064879780612197845009179244966897833355462192413675642089857015121101354157 : Int) + (4050561185128379785245378439216316270263520393631616687923865882816042088086 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (7779818828 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (7779818828 : Nat) = 3889909414 + 3889909414 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


set_option pp.all true in
#check @baseX
#print axioms baseX

set_option pp.all true in
#check @baseY
#print axioms baseY

set_option pp.all true in
#check @inputX
#print axioms inputX

set_option pp.all true in
#check @inputY
#print axioms inputY

set_option pp.all true in
#check @doubleX
#print axioms doubleX

set_option pp.all true in
#check @doubleY
#print axioms doubleY

set_option pp.all true in
#check @doubleSlope
#print axioms doubleSlope

set_option pp.all true in
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep032
