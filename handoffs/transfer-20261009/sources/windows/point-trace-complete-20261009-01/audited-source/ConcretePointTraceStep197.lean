import ShielddSecurity.ConcretePointTraceStep196
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep197
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25504733354073767449612356242116994149889995602194937066522614093910767300898
def inputY : F := 15552006826525393596728363244627764074434026645562725053557010621546071563880
def doubleX : F := 22427083887566916763150712603740354714112708205669018249526835344052679667908
def doubleY : F := 20238679198938448964410743809584059456647769868887049665308287247699376974501
def doubleSlope : F := 42543034918035017142356683647012059707948667017868860818741863758287169531195
def outX : F := 22427083887566916763150712603740354714112708205669018249526835344052679667908
def outY : F := 20238679198938448964410743809584059456647769868887049665308287247699376974501

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((181923487299361747169561752777246103332684547700734891722145 : Nat) • base) + ((181923487299361747169561752777246103332684547700734891722145 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep196.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15552006826525393596728363244627764074434026645562725053557010621546071563880 : Int)) * (7537097767588112987588401787218177763793691993650531669008596968896583044334 : Int) =
        (1 : Int) + (4470870202594555894803313995183179966894687228074702068429329718570753739103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (42543034918035017142356683647012059707948667017868860818741863758287169531195 : Int) * ((2 : Int) * (15552006826525393596728363244627764074434026645562725053557010621546071563880 : Int)) =
        (3 : Int) * (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) + (-40964 : Int) * (-40964 : Int) + (-11980635954988986032034970009934026373222766950330197669815568023767884133260 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int) =
        (42543034918035017142356683647012059707948667017868860818741863758287169531195 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) - (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) + (-34516632248291468844959274063692768468035283453197130053514386103577577830553 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20238679198938448964410743809584059456647769868887049665308287247699376974501 : Int) =
        (42543034918035017142356683647012059707948667017868860818741863758287169531195 : Int) * ((25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) - (22427083887566916763150712603740354714112708205669018249526835344052679667908 : Int)) - (15552006826525393596728363244627764074434026645562725053557010621546071563880 : Int) + (-2497003211671057852185057925426137653662457786528406202618942096514123322013 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (363846974598723494339123505554492206665369095401469783444290 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (363846974598723494339123505554492206665369095401469783444290 : Nat) = 181923487299361747169561752777246103332684547700734891722145 + 181923487299361747169561752777246103332684547700734891722145 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep197
