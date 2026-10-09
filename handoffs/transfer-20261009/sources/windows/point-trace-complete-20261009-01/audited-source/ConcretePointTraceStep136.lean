import ShielddSecurity.ConcretePointTraceStep135
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep136
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11152135691577290177658234308279982117740728321185277582231463731534997696582
def inputY : F := 29272855910383611843634709370384755771333993067709938725485928855475506925535
def doubleX : F := 21712481609491988449937706933163535589041967498244447083174737273346542090003
def doubleY : F := 45925682930392200598816987251190994446517958116142449760368930281384821731165
def doubleSlope : F := 51292717348820319189822616331897035528520256281480473119233996294206345198261
def addX : F := 24540671909485615994786041396287502347304589168921219187529425981708797037995
def addY : F := 21950383374920738125391128671308417804121995703277449261980049359967124868011
def addSlope : F := 51537220392694589697546031056572546492171106210194738734706885744447484412321
def outX : F := 24540671909485615994786041396287502347304589168921219187529425981708797037995
def outY : F := 21950383374920738125391128671308417804121995703277449261980049359967124868011

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((78896736062442832091556943117773580536422 : Nat) • base) + ((78896736062442832091556943117773580536422 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep135.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29272855910383611843634709370384755771333993067709938725485928855475506925535 : Int)) * (15357078998215466872366570349764748012095515657867162456645629436873052894782 : Int) =
        (1 : Int) + (17146488323795114552860207522986919399017014687710849928902058095205083366403 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (51292717348820319189822616331897035528520256281480473119233996294206345198261 : Int) * ((2 : Int) * (29272855910383611843634709370384755771333993067709938725485928855475506925535 : Int)) =
        (3 : Int) * (11152135691577290177658234308279982117740728321185277582231463731534997696582 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11152135691577290177658234308279982117740728321185277582231463731534997696582 : Int) + (-40964 : Int) * (-40964 : Int) + (50153797341510980653515795025119941193084049102399662553196817349279801804858 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int) =
        (51292717348820319189822616331897035528520256281480473119233996294206345198261 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11152135691577290177658234308279982117740728321185277582231463731534997696582 : Int) - (11152135691577290177658234308279982117740728321185277582231463731534997696582 : Int) + (-50174481578482425165237380590897662499779292165490111538595454818534822685794 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45925682930392200598816987251190994446517958116142449760368930281384821731165 : Int) =
        (51292717348820319189822616331897035528520256281480473119233996294206345198261 : Int) * ((11152135691577290177658234308279982117740728321185277582231463731534997696582 : Int) - (21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int)) - (29272855910383611843634709370384755771333993067709938725485928855475506925535 : Int) + (10330119149614508551475190508136309212596100998507203833507088266145686536237 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((78896736062442832091556943117773580536422 : Nat) • base) + ((78896736062442832091556943117773580536422 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (51021751776795485706678597709700511500250174423004881640849458709221820994958 : Int) =
        (1 : Int) + (-17483164888861451924385488713259069354434855953828268876185823609006031609857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (51537220392694589697546031056572546492171106210194738734706885744447484412321 : Int) * ((21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (45925682930392200598816987251190994446517958116142449760368930281384821731165 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-17659795884328288508657269599910269228999992353871299324929770915932739638323 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int) =
        (51537220392694589697546031056572546492171106210194738734706885744447484412321 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-50653966905946335813085357817796685235402537795250718556940130395682874555256 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21950383374920738125391128671308417804121995703277449261980049359967124868011 : Int) =
        (51537220392694589697546031056572546492171106210194738734706885744447484412321 : Int) * ((21712481609491988449937706933163535589041967498244447083174737273346542090003 : Int) - (24540671909485615994786041396287502347304589168921219187529425981708797037995 : Int)) - (45925682930392200598816987251190994446517958116142449760368930281384821731165 : Int) + (2779720302492344862093427293755780250660846066872977477093230733744441542816 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (157793472124885664183113886235547161072845 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (157793472124885664183113886235547161072845 : Nat) = 78896736062442832091556943117773580536422 + 78896736062442832091556943117773580536422 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep136
