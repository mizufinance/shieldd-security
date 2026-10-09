import ShielddSecurity.ConcretePointTraceStep225
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep226
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 23355861320268275589718429107220870464586034462132280060957987791523229334545
def inputY : F := 29392460099502612399823253730311463111786329509682507332461234893669902030629
def doubleX : F := 20639145913498113514444700601151820662590687829275762173610409663811496417615
def doubleY : F := 18572059118343814641264727617546248227666189440711542620161424995906690078045
def doubleSlope : F := 224222123785749972519370551975287662612796969031044935791925182997866232285
def addX : F := 48656421800279876367292632588916888997534564130984080997975354180202588755998
def addY : F := 10682480107917171582802857667287591259136657361618992850795392468437179503872
def addSlope : F := 17380778751839754416022685693917333882313159212571533609942775656428282421714
def outX : F := 48656421800279876367292632588916888997534564130984080997975354180202588755998
def outY : F := 10682480107917171582802857667287591259136657361618992850795392468437179503872

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((97669428540628758220836036853838648344664592532401044389089333450677 : Nat) • base) + ((97669428540628758220836036853838648344664592532401044389089333450677 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep225.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (29392460099502612399823253730311463111786329509682507332461234893669902030629 : Int)) * (23063426060453944347895342849157485635571026097639044219831130037240453182722 : Int) =
        (1 : Int) + (25855993743813388916875518576724313300192302995476734534785612264260039126675 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (224222123785749972519370551975287662612796969031044935791925182997866232285 : Int) * ((2 : Int) * (29392460099502612399823253730311463111786329509682507332461234893669902030629 : Int)) =
        (3 : Int) * (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) + (-40964 : Int) * (-40964 : Int) + (-30957963206672232077813866465642710311355578121146305409010651139883643878017 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int) =
        (224222123785749972519370551975287662612796969031044935791925182997866232285 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) - (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) + (-958800832961804228178718938543886345983828515919136480189039797897025376 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (18572059118343814641264727617546248227666189440711542620161424995906690078045 : Int) =
        (224222123785749972519370551975287662612796969031044935791925182997866232285 : Int) * ((23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) - (20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int)) - (29392460099502612399823253730311463111786329509682507332461234893669902030629 : Int) + (-11617002599709301307695083942533569542054561154057221246936999500117640952 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((97669428540628758220836036853838648344664592532401044389089333450677 : Nat) • base) + ((97669428540628758220836036853838648344664592532401044389089333450677 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (16508590206516064766540574678695480678042326380954173202766707265805263620008 : Int) =
        (1 : Int) + (-5994772604510551569460282334754380216949317845281091698709936469002788168865 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (17380778751839754416022685693917333882313159212571533609942775656428282421714 : Int) * ((20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (18572059118343814641264727617546248227666189440711542620161424995906690078045 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-6311490866461872376125714156871553750891805290083974867170990840100981938427 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int) =
        (17380778751839754416022685693917333882313159212571533609942775656428282421714 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-5761160064773864773605110646600450828045928824379590618378032757513310681036 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (10682480107917171582802857667287591259136657361618992850795392468437179503872 : Int) =
        (17380778751839754416022685693917333882313159212571533609942775656428282421714 : Int) * ((20639145913498113514444700601151820662590687829275762173610409663811496417615 : Int) - (48656421800279876367292632588916888997534564130984080997975354180202588755998 : Int)) - (18572059118343814641264727617546248227666189440711542620161424995906690078045 : Int) + (9286811210665310871465527356822734250995733214337451306144621524711966416683 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (195338857081257516441672073707677296689329185064802088778178666901355 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (195338857081257516441672073707677296689329185064802088778178666901355 : Nat) = 97669428540628758220836036853838648344664592532401044389089333450677 + 97669428540628758220836036853838648344664592532401044389089333450677 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep226
