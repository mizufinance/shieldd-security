import ShielddSecurity.ConcretePointTraceStep109
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep110
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 29029775996875346494901481645759474129371539048410124523547708471579330733989
def inputY : F := 6438861877568413578239490431177503265792099384497642227331954877855547034965
def doubleX : F := 48948668730282662111445423613848941049527669830922896772893048352256472257204
def doubleY : F := 26106508347555709575000823287267121841826368098806271386489767925392689735808
def doubleSlope : F := 11159431927185148731340157693276120908582382175233339888479574567317230539709
def addX : F := 5777692232401321805871635376245319506092271805702286665435652113265054685369
def addY : F := 24063447353574249502388842604895712446190708337747710149904611869615006664861
def addSlope : F := 14744204460413009893128308097485261107261593857772253946456168713838119267096
def outX : F := 5777692232401321805871635376245319506092271805702286665435652113265054685369
def outY : F := 24063447353574249502388842604895712446190708337747710149904611869615006664861

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1175652981734914065771653400626384 : Nat) • base) + ((1175652981734914065771653400626384 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep109.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (6438861877568413578239490431177503265792099384497642227331954877855547034965 : Int)) * (38993568024822886541720861423229295080611537600090670531282650394475997241290 : Int) =
        (1 : Int) + (9576428267359362151531778809543926391284243143085813919298352450067072524323 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (11159431927185148731340157693276120908582382175233339888479574567317230539709 : Int) * ((2 : Int) * (6438861877568413578239490431177503265792099384497642227331954877855547034965 : Int)) =
        (3 : Int) * (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) + (-40964 : Int) * (-40964 : Int) + (-45474126134064226893623349420302828199301465897211072999163841410039851043145 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int) =
        (11159431927185148731340157693276120908582382175233339888479574567317230539709 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) - (29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) + (-2374956468668867712116092195016107962184481530723927031830529913364935866259 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (26106508347555709575000823287267121841826368098806271386489767925392689735808 : Int) =
        (11159431927185148731340157693276120908582382175233339888479574567317230539709 : Int) * ((29029775996875346494901481645759474129371539048410124523547708471579330733989 : Int) - (48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int)) - (6438861877568413578239490431177503265792099384497642227331954877855547034965 : Int) + (4239149757317403537845891399682697284061888473270545547725052909429698551016 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1175652981734914065771653400626384 : Nat) • base) + ((1175652981734914065771653400626384 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (14127125293041608092031725518825737664039118278922592972242684411279672228212 : Int) =
        (1 : Int) + (2497081566241215043430035431599190114788501625047645781268104965944945712627 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (14744204460413009893128308097485261107261593857772253946456168713838119267096 : Int) * ((48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (26106508347555709575000823287267121841826368098806271386489767925392689735808 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (2606155208740413521027865253096194777813145481566283976956548551092801291458 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) =
        (14744204460413009893128308097485261107261593857772253946456168713838119267096 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4145855570149539870145313510742349360380393399820903120351519885656552128456 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (24063447353574249502388842604895712446190708337747710149904611869615006664861 : Int) =
        (14744204460413009893128308097485261107261593857772253946456168713838119267096 : Int) * ((48948668730282662111445423613848941049527669830922896772893048352256472257204 : Int) - (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int)) - (26106508347555709575000823287267121841826368098806271386489767925392689735808 : Int) + (-12139049879773756367927062013598476071327843617140886232644684484188045715307 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2351305963469828131543306801252769 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2351305963469828131543306801252769 : Nat) = 1175652981734914065771653400626384 + 1175652981734914065771653400626384 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
#check @addX
#print axioms addX

set_option pp.all true in
#check @addY
#print axioms addY

set_option pp.all true in
#check @addSlope
#print axioms addSlope

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
#check @next_add
#print axioms next_add

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep110
