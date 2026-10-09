import ShielddSecurity.ConcretePointTraceStep052
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep053
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 42692087916442937617659214643635058941731357804021911750260738541021161676233
def inputY : F := 3712291791224269883751889039740385755301412483453517449260650182601032756043
def doubleX : F := 45812760552077659989191185131240874644822596515033921572897724250895755032678
def doubleY : F := 10951257807955434224754146695209291026437045154459722137853659197384939693887
def doubleSlope : F := 23932533737994774854444498222651167730674082861557418512990657955651584553412
def outX : F := 45812760552077659989191185131240874644822596515033921572897724250895755032678
def outY : F := 10951257807955434224754146695209291026437045154459722137853659197384939693887

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((8157731308070751 : Nat) • base) + ((8157731308070751 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep052.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3712291791224269883751889039740385755301412483453517449260650182601032756043 : Int)) * (11239276007893228741884707157061583074234174136167210724057325702741800053847 : Int) =
        (1 : Int) + (1591409390004731814024435208429413596419083242423098121649844746235432875257 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (23932533737994774854444498222651167730674082861557418512990657955651584553412 : Int) * ((2 : Int) * (3712291791224269883751889039740385755301412483453517449260650182601032756043 : Int)) =
        (3 : Int) * (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) + (-40964 : Int) * (-40964 : Int) + (-100888065608712067386231496359507948126635952594585294565914358018847987997211 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int) =
        (23932533737994774854444498222651167730674082861557418512990657955651584553412 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) - (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) + (-10923173670837463049491289397603953638413316794010036562132530761097107925536 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (10951257807955434224754146695209291026437045154459722137853659197384939693887 : Int) =
        (23932533737994774854444498222651167730674082861557418512990657955651584553412 : Int) * ((42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) - (45812760552077659989191185131240874644822596515033921572897724250895755032678 : Int)) - (3712291791224269883751889039740385755301412483453517449260650182601032756043 : Int) + (1424322620498444503702917947694988863693180633365952482416621124608421625790 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (16315462616141502 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (16315462616141502 : Nat) = 8157731308070751 + 8157731308070751 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep053
