import ShielddSecurity.ConcretePointTraceStep163
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep164
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11707724010248953370437236779096914052462899176762174687169726617337109660280
def inputY : F := 16398859468295218015857475547959228430893047628913126055031874553951297577848
def doubleX : F := 6564796189426843237781445087258672612973778441395390039235367629045439701439
def doubleY : F := 48586230372181361358409750333122868832048372056556857148006616595896692327548
def doubleSlope : F := 31505701862728761169091644143824480190847059099337312296433920715932157391836
def addX : F := 17119618191088622730098396381817294085596503852139435327869958331837476286695
def addY : F := 45402685746424772580864703624291120796294168146642407233914930396477023310166
def addSlope : F := 44032872118625083312473770241020672179720799840032491510779474897342020399286
def outX : F := 17119618191088622730098396381817294085596503852139435327869958331837476286695
def outY : F := 45402685746424772580864703624291120796294168146642407233914930396477023310166

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((21178681321833486106428521775785612796047300531148 : Nat) • base) + ((21178681321833486106428521775785612796047300531148 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep163.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16398859468295218015857475547959228430893047628913126055031874553951297577848 : Int)) * (28119311623921166791180741485791347090117631688014943009110497371788672736058 : Int) =
        (1 : Int) + (17588135532240544169628266320109023929311835654979992743481096758121899057759 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (31505701862728761169091644143824480190847059099337312296433920715932157391836 : Int) * ((2 : Int) * (16398859468295218015857475547959228430893047628913126055031874553951297577848 : Int)) =
        (3 : Int) * (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) + (-40964 : Int) * (-40964 : Int) + (11864067263407033001057870696058660382428082728441255411764110775547702256880 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int) =
        (31505701862728761169091644143824480190847059099337312296433920715932157391836 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) - (11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) + (-18929964390753810852288135455999023022488465772302718615527770223829923724905 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (48586230372181361358409750333122868832048372056556857148006616595896692327548 : Int) =
        (31505701862728761169091644143824480190847059099337312296433920715932157391836 : Int) * ((11707724010248953370437236779096914052462899176762174687169726617337109660280 : Int) - (6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int)) - (16398859468295218015857475547959228430893047628913126055031874553951297577848 : Int) + (-3090089563360945348899708323289822539561023385237860247882734127980178084360 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((21178681321833486106428521775785612796047300531148 : Nat) • base) + ((21178681321833486106428521775785612796047300531148 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (39214085254436678957798400843818654031113186375694985324341877125333952361594 : Int) =
        (1 : Int) + (-24765310254139475343147930396801294097865026247492707852987602480463693027849 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (44032872118625083312473770241020672179720799840032491510779474897342020399286 : Int) * ((6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (48586230372181361358409750333122868832048372056556857148006616595896692327548 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-27808572667781923355893895793037229944837710276752719817065425199937385530122 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int) =
        (44032872118625083312473770241020672179720799840032491510779474897342020399286 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-36976474990445778402888375339270793141148034070321195003215436103980235114419 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (45402685746424772580864703624291120796294168146642407233914930396477023310166 : Int) =
        (44032872118625083312473770241020672179720799840032491510779474897342020399286 : Int) * ((6564796189426843237781445087258672612973778441395390039235367629045439701439 : Int) - (17119618191088622730098396381817294085596503852139435327869958331837476286695 : Int)) - (48586230372181361358409750333122868832048372056556857148006616595896692327548 : Int) + (8863380765207283273013239391420021810598835815763033994602373984819878124610 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (42357362643666972212857043551571225592094601062297 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (42357362643666972212857043551571225592094601062297 : Nat) = 21178681321833486106428521775785612796047300531148 + 21178681321833486106428521775785612796047300531148 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep164
