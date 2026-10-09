import ShielddSecurity.ConcretePointTraceStep004
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep005
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 27416318839537145010600649894766761814387953753752631843700945536134826640529
def inputY : F := 1470886311888350237318958292419739516514468566140978908671109266579203296049
def doubleX : F := 12080065405981109434320689981986723253450098380364271283015225325571931429470
def doubleY : F := 33062009996441556713628343913323655147968284039017132475139379903737815695083
def doubleSlope : F := 28974383614506599228792545071592532926566071788434575284386643851388466318855
def addX : F := 41283911756810255122586575491328845087064416522079797081782609301767538420142
def addY : F := 2915854498086107523456245359524550650266537620604363330686602258345388509879
def addSlope : F := 45136453920122113598797017277610930938305534210621429981326834320718408684829
def outX : F := 41283911756810255122586575491328845087064416522079797081782609301767538420142
def outY : F := 2915854498086107523456245359524550650266537620604363330686602258345388509879

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((28 : Nat) • base) + ((28 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep004.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1470886311888350237318958292419739516514468566140978908671109266579203296049 : Int)) * (25736891519268530708317954226778402831240895683168333665598173406384862872679 : Int) =
        (1 : Int) + (1443898526335842552943005934179467878413032828355550956689361124476140194157 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (28974383614506599228792545071592532926566071788434575284386643851388466318855 : Int) * ((2 : Int) * (1470886311888350237318958292419739516514468566140978908671109266579203296049 : Int)) =
        (3 : Int) * (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) + (-40964 : Int) * (-40964 : Int) + (-41378685115467739384800630625849969095100619774173932364846869241648001240245 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int) =
        (28974383614506599228792545071592532926566071788434575284386643851388466318855 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) - (27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) + (-16010315514650283557368637645317801139365586022960224097971445941808864338105 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33062009996441556713628343913323655147968284039017132475139379903737815695083 : Int) =
        (28974383614506599228792545071592532926566071788434575284386643851388466318855 : Int) * ((27416318839537145010600649894766761814387953753752631843700945536134826640529 : Int) - (12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int)) - (1470886311888350237318958292419739516514468566140978908671109266579203296049 : Int) + (-8474321992511250010979607918393838703609553139200327220673948097560825718601 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((28 : Nat) • base) + ((28 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (492438228597945134331209416084337446664432357544068497812305772158691376402 : Int) =
        (1 : Int) + (-259199774586612503234186642362846268619198608070422005950165236193560872379 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (45136453920122113598797017277610930938305534210621429981326834320718408684829 : Int) * ((12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (33062009996441556713628343913323655147968284039017132475139379903737815695083 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-23758022838813155587526380415945822762008016240144623102791878558528683539778 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int) =
        (45136453920122113598797017277610930938305534210621429981326834320718408684829 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-38853160468459827076828299424217805257185899644391609278929359288958159395378 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (2915854498086107523456245359524550650266537620604363330686602258345388509879 : Int) =
        (45136453920122113598797017277610930938305534210621429981326834320718408684829 : Int) * ((12080065405981109434320689981986723253450098380364271283015225325571931429470 : Int) - (41283911756810255122586575491328845087064416522079797081782609301767538420142 : Int)) - (33062009996441556713628343913323655147968284039017132475139379903737815695083 : Int) + (25138477439388973417803396292628736067837369058315873077227159211476887868850 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (57 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (57 : Nat) = 28 + 28 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep005
