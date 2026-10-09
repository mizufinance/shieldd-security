import ShielddSecurity.ConcretePointTraceStep051
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep052
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18162287734678238101240760966422397591443200100057241259459337599027509260642
def inputY : F := 21282273064572202846428430150050906084679599671700514532981454480643688385136
def doubleX : F := 30240814438042992711431713408349048717404416389629678842529400583584014981630
def doubleY : F := 34185752556316350702157254743578012770187642398355410390178182516342728543495
def doubleSlope : F := 9051662927354181352421536379844070084147159516413624258423749314639407847759
def addX : F := 42692087916442937617659214643635058941731357804021911750260738541021161676233
def addY : F := 3712291791224269883751889039740385755301412483453517449260650182601032756043
def addSlope : F := 13643625754751373378818468224690829831896373493282777946160694025093529537590
def outX : F := 42692087916442937617659214643635058941731357804021911750260738541021161676233
def outY : F := 3712291791224269883751889039740385755301412483453517449260650182601032756043

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((4078865654035375 : Nat) • base) + ((4078865654035375 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep051.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21282273064572202846428430150050906084679599671700514532981454480643688385136 : Int)) * (51534133430746554051709829896229153385741620554624684057473320986113265998601 : Int) =
        (1 : Int) + (41832562006689453105509042804470931221419850606024461894707423173022133836767 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (9051662927354181352421536379844070084147159516413624258423749314639407847759 : Int) * ((2 : Int) * (21282273064572202846428430150050906084679599671700514532981454480643688385136 : Int)) =
        (3 : Int) * (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) + (-40964 : Int) * (-40964 : Int) + (-11525051523152021196729902118784542868664929050559714126288235368940634641756 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int) =
        (9051662927354181352421536379844070084147159516413624258423749314639407847759 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) - (18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) + (-1562529498683834858237069154437389849226616765215232466123842052828551350695 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34185752556316350702157254743578012770187642398355410390178182516342728543495 : Int) =
        (9051662927354181352421536379844070084147159516413624258423749314639407847759 : Int) * ((18162287734678238101240760966422397591443200100057241259459337599027509260642 : Int) - (30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int)) - (21282273064572202846428430150050906084679599671700514532981454480643688385136 : Int) + (2085037238584454551115857971035191272737095193584172265102244646603110095771 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((4078865654035375 : Nat) • base) + ((4078865654035375 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (43037686325469060159193673197656806702072255148728245118511198620936564789079 : Int) =
        (1 : Int) + (-7747554631829687461731372943024663786182352979093488224420023214502970256676 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (13643625754751373378818468224690829831896373493282777946160694025093529537590 : Int) * ((30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34185752556316350702157254743578012770187642398355410390178182516342728543495 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2456097084582828373185278497605704413092487917533018852953471657619322585163 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int) =
        (13643625754751373378818468224690829831896373493282777946160694025093529537590 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-3550022253161849774935566762408188890649813914527738301941624196398160002194 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (3712291791224269883751889039740385755301412483453517449260650182601032756043 : Int) =
        (13643625754751373378818468224690829831896373493282777946160694025093529537590 : Int) * ((30240814438042992711431713408349048717404416389629678842529400583584014981630 : Int) - (42692087916442937617659214643635058941731357804021911750260738541021161676233 : Int)) - (34185752556316350702157254743578012770187642398355410390178182516342728543495 : Int) + (3239776487795435704016479711945020972863780180824948243847427298322817255716 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (8157731308070751 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (8157731308070751 : Nat) = 4078865654035375 + 4078865654035375 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep052
