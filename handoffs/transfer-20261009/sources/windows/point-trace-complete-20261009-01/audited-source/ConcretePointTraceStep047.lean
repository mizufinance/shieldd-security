import ShielddSecurity.ConcretePointTraceStep046
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep047
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 49247472984684596498223657552728494939904532011843055046126173280548413673307
def inputY : F := 11438903628521316103570136825836017673458105972056446291778971950032122130410
def doubleX : F := 25153231165935098296941729463853780492694250103819268966501968632169823924349
def doubleY : F := 41984835228654144156636091704408006412901450578268278489830927569996550296479
def doubleSlope : F := 42376176610847604167793634870020254246174140534865536455730175494036167652986
def outX : F := 25153231165935098296941729463853780492694250103819268966501968632169823924349
def outY : F := 41984835228654144156636091704408006412901450578268278489830927569996550296479

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((127464551688605 : Nat) • base) + ((127464551688605 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep046.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (11438903628521316103570136825836017673458105972056446291778971950032122130410 : Int)) * (24774547991807033175252378444843808221685073098756908889471457368036686762298 : Int) =
        (1 : Int) + (10809151786709925963123464887306409108478145945332210011030755738553056283143 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (42376176610847604167793634870020254246174140534865536455730175494036167652986 : Int) * ((2 : Int) * (11438903628521316103570136825836017673458105972056446291778971950032122130410 : Int)) =
        (3 : Int) * (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) + (-40964 : Int) * (-40964 : Int) + (-120270077771676497355407121940452137464731707335396318487304538684669049210467 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) =
        (42376176610847604167793634870020254246174140534865536455730175494036167652986 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) - (49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) + (-34246407410123406400260632198684641896856511493422526788359105270516435542777 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (41984835228654144156636091704408006412901450578268278489830927569996550296479 : Int) =
        (42376176610847604167793634870020254246174140534865536455730175494036167652986 : Int) * ((49247472984684596498223657552728494939904532011843055046126173280548413673307 : Int) - (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int)) - (11438903628521316103570136825836017673458105972056446291778971950032122130410 : Int) + (-19471818544188941665623481601945664858022796553985551413426553380653552928323 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (254929103377210 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (254929103377210 : Nat) = 127464551688605 + 127464551688605 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep047
