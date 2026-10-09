import ShielddSecurity.ConcretePointTraceStep203
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep204
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22654833802152741492955822644190109173062412335261798635205989424837512510783
def inputY : F := 3317576814041047444775866956284789662008526847095044842404141569430213747165
def doubleX : F := 16810720316566490990751060652421470777556901491962546143899626636772648017141
def doubleY : F := 20066309154940202382437977043853789027233261813845634108541543434177679150734
def doubleSlope : F := 14666886416342986655021329675586453970128476996694501987471114875951457261333
def outX : F := 16810720316566490990751060652421470777556901491962546143899626636772648017141
def outY : F := 20066309154940202382437977043853789027233261813845634108541543434177679150734

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((23286206374318303637703904355487501226583622105694066140434583 : Nat) • base) + ((23286206374318303637703904355487501226583622105694066140434583 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep203.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3317576814041047444775866956284789662008526847095044842404141569430213747165 : Int)) * (24997250569837016368825739695110436760416145747873027018228785607764655242976 : Int) =
        (1 : Int) + (3163112988132406780381681247704447013999016175550515740852131849045232635583 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (14666886416342986655021329675586453970128476996694501987471114875951457261333 : Int) * ((2 : Int) * (3317576814041047444775866956284789662008526847095044842404141569430213747165 : Int)) =
        (3 : Int) * (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) + (-40964 : Int) * (-40964 : Int) + (-27508026410812164165986798080899442446339098244164582715142546312382923778145 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) =
        (14666886416342986655021329675586453970128476996694501987471114875951457261333 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) - (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) + (-4102488161615559851879175384010085916166431912884907838183824603633476022350 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20066309154940202382437977043853789027233261813845634108541543434177679150734 : Int) =
        (14666886416342986655021329675586453970128476996694501987471114875951457261333 : Int) * ((22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) - (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int)) - (3317576814041047444775866956284789662008526847095044842404141569430213747165 : Int) + (-1634662307266535737817164404150179699239164128970851607406773384023297317799 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (46572412748636607275407808710975002453167244211388132280869166 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (46572412748636607275407808710975002453167244211388132280869166 : Nat) = 23286206374318303637703904355487501226583622105694066140434583 + 23286206374318303637703904355487501226583622105694066140434583 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep204
