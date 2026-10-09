import ShielddSecurity.ConcretePointTraceStep214
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep215
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 5254431352040567715800818809815540178997839561488166687536101363101735459962
def inputY : F := 45089967721278676411666858878152654011380270001749389418729351942356335091858
def doubleX : F := 28102607984511849083212898408965767073496639322156664565137191600391141085232
def doubleY : F := 19673666312670772715897332549439440762112409562875706226251978831939803071885
def doubleSlope : F := 40826080660252124290347240517473204934621134346100188538654451744854492150738
def addX : F := 2472871116929812212281188731644840928172978252295042402628337375621512375572
def addY : F := 15626333237137253335437934225429213444962979570757477153778973902077750255117
def addSlope : F := 49319395061618793493029943674481312572461022989978989484359052565014624007482
def outX : F := 2472871116929812212281188731644840928172978252295042402628337375621512375572
def outY : F := 15626333237137253335437934225429213444962979570757477153778973902077750255117

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((47690150654603885850017596120038402512043258072461447455610026098 : Nat) • base) + ((47690150654603885850017596120038402512043258072461447455610026098 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep214.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (45089967721278676411666858878152654011380270001749389418729351942356335091858 : Int)) * (1677448545933050502632189103157145223270148889198903339031344020700976031162 : Int) =
        (1 : Int) + (2884898956587123462311493195855265443305743699141015620633868792160769312807 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40826080660252124290347240517473204934621134346100188538654451744854492150738 : Int) * ((2 : Int) * (45089967721278676411666858878152654011380270001749389418729351942356335091858 : Int)) =
        (3 : Int) * (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) + (-40964 : Int) * (-40964 : Int) + (68633662731759569894190071393123735402533002671881617268869894509989510628524 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int) =
        (40826080660252124290347240517473204934621134346100188538654451744854492150738 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) - (5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) + (-31786803529276677832253162429311145894684076368764444006307529655445799087912 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (19673666312670772715897332549439440762112409562875706226251978831939803071885 : Int) =
        (40826080660252124290347240517473204934621134346100188538654451744854492150738 : Int) * ((5254431352040567715800818809815540178997839561488166687536101363101735459962 : Int) - (28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int)) - (45089967721278676411666858878152654011380270001749389418729351942356335091858 : Int) + (17789376052589465312868375606706801641586513639204057271733834620678881018731 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((47690150654603885850017596120038402512043258072461447455610026098 : Nat) • base) + ((47690150654603885850017596120038402512043258072461447455610026098 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (27663443799660210831691130833515564421152947167666696669681652413212276411086 : Int) =
        (1 : Int) + (-6107962948241944107107046170683158204355238825030995982590121596817019209899 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (49319395061618793493029943674481312572461022989978989484359052565014624007482 : Int) * ((28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (19673666312670772715897332549439440762112409562875706226251978831939803071885 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-10889498785750400255402907671890868010168258627460734279276155978906860382417 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) =
        (49319395061618793493029943674481312572461022989978989484359052565014624007482 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-46388140202108765386052883363047658584048884469060256113815117447305465654485 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15626333237137253335437934225429213444962979570757477153778973902077750255117 : Int) =
        (49319395061618793493029943674481312572461022989978989484359052565014624007482 : Int) * ((28102607984511849083212898408965767073496639322156664565137191600391141085232 : Int) - (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int)) - (19673666312670772715897332549439440762112409562875706226251978831939803071885 : Int) + (-24106456003183752132834522718864546987539685336881327609230363246920979537086 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (95380301309207771700035192240076805024086516144922894911220052197 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (95380301309207771700035192240076805024086516144922894911220052197 : Nat) = 47690150654603885850017596120038402512043258072461447455610026098 + 47690150654603885850017596120038402512043258072461447455610026098 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep215
