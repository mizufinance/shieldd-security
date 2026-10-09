import ShielddSecurity.ConcretePointTraceStep176
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep177
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28775296852505744947996206910410988101402576837126816807998287590104983744432
def inputY : F := 27492392060764410741441622795304753493806197639329667585137468569762792367114
def doubleX : F := 41675841784311437110671266299111971491936841048584217071604886606650932902661
def doubleY : F := 13861758892827646495578889041375087890991535615956654582845615209234125345271
def doubleSlope : F := 35121716254930957375328768193760056339748178638316278660024199833361631736336
def outX : F := 41675841784311437110671266299111971491936841048584217071604886606650932902661
def outY : F := 13861758892827646495578889041375087890991535615956654582845615209234125345271

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((173495757388459918183862450387235740025219485951170818 : Nat) • base) + ((173495757388459918183862450387235740025219485951170818 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep176.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (27492392060764410741441622795304753493806197639329667585137468569762792367114 : Int)) * (18989748941009179808188825983808665934749838479497781109084205249867573983060 : Int) =
        (1 : Int) + (19912841018790290303794324369140070708754118128088028195250145575626156208783 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (35121716254930957375328768193760056339748178638316278660024199833361631736336 : Int) * ((2 : Int) * (27492392060764410741441622795304753493806197639329667585137468569762792367114 : Int)) =
        (3 : Int) * (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) + (-40964 : Int) * (-40964 : Int) + (-10544176839767643106345348833827788677655461926777060048369074217478261892816 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int) =
        (35121716254930957375328768193760056339748178638316278660024199833361631736336 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) - (28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) + (-23524637446635558110533102653076732965279964784747526584495114214306529994403 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (13861758892827646495578889041375087890991535615956654582845615209234125345271 : Int) =
        (35121716254930957375328768193760056339748178638316278660024199833361631736336 : Int) * ((28775296852505744947996206910410988101402576837126816807998287590104983744432 : Int) - (41675841784311437110671266299111971491936841048584217071604886606650932902661 : Int)) - (27492392060764410741441622795304753493806197639329667585137468569762792367114 : Int) + (8640826096935203245829546009799863636766170675259279738782182956054351594833 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (346991514776919836367724900774471480050438971902341636 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (346991514776919836367724900774471480050438971902341636 : Nat) = 173495757388459918183862450387235740025219485951170818 + 173495757388459918183862450387235740025219485951170818 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep177
