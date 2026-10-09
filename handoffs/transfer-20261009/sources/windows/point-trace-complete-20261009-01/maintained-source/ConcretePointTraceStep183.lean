import ShielddSecurity.ConcretePointTraceStep182
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep183
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 29058457557077696265914094575592691247089204207831356146859749805977571019394
def inputY : F := 8614489095074981705477209038505227660466779104797669514251599867465035617300
def doubleX : F := 43757500933763341425818136817149715342039627569793424573198778816067373963464
def doubleY : F := 48008767005075130188619138434974610680629315432845505254802505996585524882135
def doubleSlope : F := 41485405177625565721562954475461494870403626437858751012058526368260820115729
def outX : F := 43757500933763341425818136817149715342039627569793424573198778816067373963464
def outY : F := 48008767005075130188619138434974610680629315432845505254802505996585524882135

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((11103728472861434763767196824783087361614047100874932356 : Nat) • base) + ((11103728472861434763767196824783087361614047100874932356 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep182.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8614489095074981705477209038505227660466779104797669514251599867465035617300 : Int)) * (24523820265575528257172229237547763160898836991345751879660306099106033718559 : Int) =
        (1 : Int) + (8057849002874807763675655443850311975566761389182015023466116711629964715223 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (41485405177625565721562954475461494870403626437858751012058526368260820115729 : Int) * ((2 : Int) * (8614489095074981705477209038505227660466779104797669514251599867465035617300 : Int)) =
        (3 : Int) * (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) + (-40964 : Int) * (-40964 : Int) + (-34679133698091007583583328037907128773858624716763532747955259926612571046740 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int) =
        (41485405177625565721562954475461494870403626437858751012058526368260820115729 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) - (29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) + (-32821781595211456291314310799633726969106149423473063003951969815577195607389 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (48008767005075130188619138434974610680629315432845505254802505996585524882135 : Int) =
        (41485405177625565721562954475461494870403626437858751012058526368260820115729 : Int) * ((29058457557077696265914094575592691247089204207831356146859749805977571019394 : Int) - (43757500933763341425818136817149715342039627569793424573198778816067373963464 : Int)) - (8614489095074981705477209038505227660466779104797669514251599867465035617300 : Int) + (11629361923848731256303435960557362004613447811853791660981218545450989500305 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (22207456945722869527534393649566174723228094201749864712 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (22207456945722869527534393649566174723228094201749864712 : Nat) = 11103728472861434763767196824783087361614047100874932356 + 11103728472861434763767196824783087361614047100874932356 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep183
