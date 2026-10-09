import ShielddSecurity.ConcretePointTraceStep181
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep182
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28001849522585207766373342824886941819777921447563607012500415465115141660056
def inputY : F := 42724231404024003359570834440145114107396506321853472808075686206927141823351
def doubleX : F := 29058457557077696265914094575592691247089204207831356146859749805977571019394
def doubleY : F := 8614489095074981705477209038505227660466779104797669514251599867465035617300
def doubleSlope : F := 24183719901419160496778623725459824957174167105207132853237052757909286409369
def outX : F := 29058457557077696265914094575592691247089204207831356146859749805977571019394
def outY : F := 8614489095074981705477209038505227660466779104797669514251599867465035617300

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5551864236430717381883598412391543680807023550437466178 : Nat) • base) + ((5551864236430717381883598412391543680807023550437466178 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep181.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42724231404024003359570834440145114107396506321853472808075686206927141823351 : Int)) * (41001758508472368798174618752852864480869352180508404403090288976399567814751 : Int) =
        (1 : Int) + (66815652933694657624701265904903429870754134938531334286592194888320834064977 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24183719901419160496778623725459824957174167105207132853237052757909286409369 : Int) * ((2 : Int) * (42724231404024003359570834440145114107396506321853472808075686206927141823351 : Int)) =
        (3 : Int) * (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) + (-40964 : Int) * (-40964 : Int) + (-5451402089603109711261745659755856418179423513394272191902933870769845733650 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) =
        (24183719901419160496778623725459824957174167105207132853237052757909286409369 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) - (28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) + (-11153667337810190049288775356237346021459581984597408707016681708682784931271 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (8614489095074981705477209038505227660466779104797669514251599867465035617300 : Int) =
        (24183719901419160496778623725459824957174167105207132853237052757909286409369 : Int) * ((28001849522585207766373342824886941819777921447563607012500415465115141660056 : Int) - (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int)) - (42724231404024003359570834440145114107396506321853472808075686206927141823351 : Int) + (487313555202693011575601176258603449123059404715597790486359313240623077221 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (11103728472861434763767196824783087361614047100874932356 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (11103728472861434763767196824783087361614047100874932356 : Nat) = 5551864236430717381883598412391543680807023550437466178 + 5551864236430717381883598412391543680807023550437466178 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep182
