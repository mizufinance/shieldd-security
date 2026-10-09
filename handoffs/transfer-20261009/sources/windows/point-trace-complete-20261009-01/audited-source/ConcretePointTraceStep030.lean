import ShielddSecurity.ConcretePointTraceStep029
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep030
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 21096557341129318036935165035116531548878001934455463800463554823722073269553
def inputY : F := 1688460704591636169008746998165317674695270965295441312037947241562229018264
def doubleX : F := 14623691323707468481687329662612064867450834205841337028494115445574018414170
def doubleY : F := 9631382760839044233923589704243406850048360561442482355769296858926269946874
def doubleSlope : F := 44948240041063082634600362686389502790790664646481705366997713011352105626348
def addX : F := 35904030519016117224290495438111213184051551672982889471995665290012844512132
def addY : F := 16105951619558771069147932775113008581324909718474116609394308486113511240245
def addSlope : F := 21633756187105829907438661765123021514817241065531715184515070334717090689710
def outX : F := 35904030519016117224290495438111213184051551672982889471995665290012844512132
def outY : F := 16105951619558771069147932775113008581324909718474116609394308486113511240245

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((972477353 : Nat) • base) + ((972477353 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep029.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1688460704591636169008746998165317674695270965295441312037947241562229018264 : Int)) * (453185882027783407805307747068554890351736393757034488801260637123901799101 : Int) =
        (1 : Int) + (29185611992706548974237429584504062920676482883474468342188513766430829679 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (44948240041063082634600362686389502790790664646481705366997713011352105626348 : Int) * ((2 : Int) * (1688460704591636169008746998165317674695270965295441312037947241562229018264 : Int)) =
        (3 : Int) * (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) + (-40964 : Int) * (-40964 : Int) + (-22568661567877593472386631732910679557042291605628269321797280122739601047267 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int) =
        (44948240041063082634600362686389502790790664646481705366997713011352105626348 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) - (21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) + (-38529809525281075722006393109345580774379967477814903058896692586459320912092 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (9631382760839044233923589704243406850048360561442482355769296858926269946874 : Int) =
        (44948240041063082634600362686389502790790664646481705366997713011352105626348 : Int) * ((21096557341129318036935165035116531548878001934455463800463554823722073269553 : Int) - (14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int)) - (1688460704591636169008746998165317674695270965295441312037947241562229018264 : Int) + (-5548566406740004048271304076254816560753702799088730700374028374218233678242 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((972477353 : Nat) • base) + ((972477353 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (47822190483998207966630700499346572050452459141046585013150791509358505278192 : Int) =
        (1 : Int) + (-22851867623375381217828328738728038272296347495989415023074520980211698112369 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (21633756187105829907438661765123021514817241065531715184515070334717090689710 : Int) * ((14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (9631382760839044233923589704243406850048360561442482355769296858926269946874 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-10337705729927665431229718464933825661396753527711237386935954258794735898766 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int) =
        (21633756187105829907438661765123021514817241065531715184515070334717090689710 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-8925557267806457574734090644081445207824166043283667513818397714683090156891 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (16105951619558771069147932775113008581324909718474116609394308486113511240245 : Int) =
        (21633756187105829907438661765123021514817241065531715184515070334717090689710 : Int) * ((14623691323707468481687329662612064867450834205841337028494115445574018414170 : Int) - (35904030519016117224290495438111213184051551672982889471995665290012844512132 : Int)) - (9631382760839044233923589704243406850048360561442482355769296858926269946874 : Int) + (8779746084005572375181278033812424726980045754778332817604718434822064854203 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1944954707 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1944954707 : Nat) = 972477353 + 972477353 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep030
