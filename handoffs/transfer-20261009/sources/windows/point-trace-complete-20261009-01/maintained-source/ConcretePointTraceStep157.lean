import ShielddSecurity.ConcretePointTraceStep156
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep157
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12097625452536914439360317234161396025970551999657340922646029728917320644396
def inputY : F := 10904485311615268752083358961102852905051872603172247544652655847981267497571
def doubleX : F := 23945330906640122588891774370931833721844591321012405216405429023970138139913
def doubleY : F := 27246132892169293347978502701946911338232740368971889646397031540238716356524
def doubleSlope : F := 4829890360018109460185333633219342088034934979307912299860736143843365069986
def addX : F := 32519754935291984064399895721098749478758911878471915533641312939975545696476
def addY : F := 42956781121015365294969681217312514003994247563580404675698060438768365327098
def addSlope : F := 16465282188969026839782581600422992091558843544511686335479247289007432575024
def outX : F := 32519754935291984064399895721098749478758911878471915533641312939975545696476
def outY : F := 42956781121015365294969681217312514003994247563580404675698060438768365327098

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((165458447826824110206472826373325099969119535399 : Nat) • base) + ((165458447826824110206472826373325099969119535399 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep156.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (10904485311615268752083358961102852905051872603172247544652655847981267497571 : Int)) * (1460611842413613014474379307877791819870198155500458049954524381281920627324 : Int) =
        (1 : Int) + (607493260229816648443093834738438939550397846484311007188549971996442328039 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (4829890360018109460185333633219342088034934979307912299860736143843365069986 : Int) * ((2 : Int) * (10904485311615268752083358961102852905051872603172247544652655847981267497571 : Int)) =
        (3 : Int) * (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) + (-40964 : Int) * (-40964 : Int) + (-6364396258858561362541354297631889071360069503635273531290524868438704963252 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int) =
        (4829890360018109460185333633219342088034934979307912299860736143843365069986 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) - (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) + (-444883218061778502350757262640577700052108626169684940688272518151702649643 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27246132892169293347978502701946911338232740368971889646397031540238716356524 : Int) =
        (4829890360018109460185333633219342088034934979307912299860736143843365069986 : Int) * ((12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) - (23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int)) - (10904485311615268752083358961102852905051872603172247544652655847981267497571 : Int) + (1091297097073184336963905227243224434743186854613943391581423848502077760489 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((165458447826824110206472826373325099969119535399 : Nat) • base) + ((165458447826824110206472826373325099969119535399 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (7953316326935895153234722843930334585671942184450475546350691927325120857264 : Int) =
        (1 : Int) + (-2386619502176004594192983300522414660887011775864575644380528818974726426337 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (16465282188969026839782581600422992091558843544511686335479247289007432575024 : Int) * ((23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (27246132892169293347978502701946911338232740368971889646397031540238716356524 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4940877737747929040719681194877364529390534479930047685944882136271968071266 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int) =
        (16465282188969026839782581600422992091558843544511686335479247289007432575024 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-5170229669228138983067070026724910013076789503796810400121147359337009251344 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42956781121015365294969681217312514003994247563580404675698060438768365327098 : Int) =
        (16465282188969026839782581600422992091558843544511686335479247289007432575024 : Int) * ((23945330906640122588891774370931833721844591321012405216405429023970138139913 : Int) - (32519754935291984064399895721098749478758911878471915533641312939975545696476 : Int)) - (27246132892169293347978502701946911338232740368971889646397031540238716356524 : Int) + (2692437396498356117295804440305117158336193891883107929051932977217826507318 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (330916895653648220412945652746650199938239070799 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (330916895653648220412945652746650199938239070799 : Nat) = 165458447826824110206472826373325099969119535399 + 165458447826824110206472826373325099969119535399 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep157
