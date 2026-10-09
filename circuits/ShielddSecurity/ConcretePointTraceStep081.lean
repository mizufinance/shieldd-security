import ShielddSecurity.ConcretePointTraceStep080
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep081
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12426011185503422633767884078312640800199031477463737358107803603538291618288
def inputY : F := 49445160941242159412468737629693755242696987535313224428994431235309232460016
def doubleX : F := 3592619559029744071302652922465033624567307736147135569179248253630476051480
def doubleY : F := 2390729998028047014141432011711265607351043552138256735345189118532694064024
def doubleSlope : F := 36267128100345636220970439205786742133810579644718746019452713167457452166543
def outX : F := 3592619559029744071302652922465033624567307736147135569179248253630476051480
def outY : F := 2390729998028047014141432011711265607351043552138256735345189118532694064024

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2189824323607448610983143 : Nat) • base) + ((2189824323607448610983143 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep080.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (49445160941242159412468737629693755242696987535313224428994431235309232460016 : Int)) * (36760189201108220672061014656292698982989166729660379121520246598693815778402 : Int) =
        (1 : Int) + (69327095817846576173881636738314260177142073869761098534057831195274815829951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36267128100345636220970439205786742133810579644718746019452713167457452166543 : Int) * ((2 : Int) * (49445160941242159412468737629693755242696987535313224428994431235309232460016 : Int)) =
        (3 : Int) * (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) + (-40964 : Int) * (-40964 : Int) + (59563241754211594044080600993161352924806151860049393724914936873670103279632 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int) =
        (36267128100345636220970439205786742133810579644718746019452713167457452166543 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) - (12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) + (-25084058886287382477861601816521149262170566509377668917102375008824860134897 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2390729998028047014141432011711265607351043552138256735345189118532694064024 : Int) =
        (36267128100345636220970439205786742133810579644718746019452713167457452166543 : Int) * ((12426011185503422633767884078312640800199031477463737358107803603538291618288 : Int) - (3592619559029744071302652922465033624567307736147135569179248253630476051480 : Int)) - (49445160941242159412468737629693755242696987535313224428994431235309232460016 : Int) + (-6109590897603825863838621356550444040107664475922116182686691456516187154208 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4379648647214897221966286 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (4379648647214897221966286 : Nat) = 2189824323607448610983143 + 2189824323607448610983143 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep081
