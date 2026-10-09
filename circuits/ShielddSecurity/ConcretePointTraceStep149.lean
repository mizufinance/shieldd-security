import ShielddSecurity.ConcretePointTraceStep148
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep149
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 6344755949005947150653169382720144082682033786605102380658736430677447133350
def inputY : F := 37902207718273805376544761773145242753796073241080595342964531779783224627171
def doubleX : F := 13893635581100041838529174086803523763978972725418931508683760845156668731886
def doubleY : F := 37981386710589963954145812023721280222085172063335852022147403838315281454010
def doubleSlope : F := 47920991146890275932908121211093921572354093309534195490469779412941107582963
def outX : F := 13893635581100041838529174086803523763978972725418931508683760845156668731886
def outY : F := 37981386710589963954145812023721280222085172063335852022147403838315281454010

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((646322061823531680494034478020801171754373185 : Nat) • base) + ((646322061823531680494034478020801171754373185 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep148.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37902207718273805376544761773145242753796073241080595342964531779783224627171 : Int)) * (38312408381929284615381833611325348778528100175367802028917490943987665984817 : Int) =
        (1 : Int) + (55386693016160706420757389795670278057874305134273593433008530307383580099301 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (47920991146890275932908121211093921572354093309534195490469779412941107582963 : Int) * ((2 : Int) * (37902207718273805376544761773145242753796073241080595342964531779783224627171 : Int)) =
        (3 : Int) * (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) + (-40964 : Int) * (-40964 : Int) + (66974279062639866368399666649307478031114965391672529232155809439553463294550 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int) =
        (47920991146890275932908121211093921572354093309534195490469779412941107582963 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) - (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) + (-43794851994568806396259963864478189196606151238967690686211309175230531915127 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (37981386710589963954145812023721280222085172063335852022147403838315281454010 : Int) =
        (47920991146890275932908121211093921572354093309534195490469779412941107582963 : Int) * ((6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) - (13893635581100041838529174086803523763978972725418931508683760845156668731886 : Int)) - (37902207718273805376544761773145242753796073241080595342964531779783224627171 : Int) + (6898898756058587316060313781606304590148431154266085526545655279093417200373 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1292644123647063360988068956041602343508746370 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1292644123647063360988068956041602343508746370 : Nat) = 646322061823531680494034478020801171754373185 + 646322061823531680494034478020801171754373185 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep149
