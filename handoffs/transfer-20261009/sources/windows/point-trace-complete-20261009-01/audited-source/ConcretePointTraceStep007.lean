import ShielddSecurity.ConcretePointTraceStep006
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep007
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 21933938387720517397777775700475712951098354028738066484391338187786808861578
def inputY : F := 16390246766700321050481125259312507925865235543189173088893915032765084532165
def doubleX : F := 34129517494893296877003897096003292625773952744021646161908021957385756966113
def doubleY : F := 43208462230955820829943285945607605018670933806571005865504367515923698639806
def doubleSlope : F := 36237182653660276449462006808171555654119938756498077708073758651832832581388
def addX : F := 18416231769129038938590376633805459194750870281549264888420309157482590710276
def addY : F := 36612701123945719380912906697697377473105333689555289375180417076038791909164
def addSlope : F := 46123018585099466238203170774973770487550977712485997628606620849870381545934
def outX : F := 18416231769129038938590376633805459194750870281549264888420309157482590710276
def outY : F := 36612701123945719380912906697697377473105333689555289375180417076038791909164

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((115 : Nat) • base) + ((115 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep006.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16390246766700321050481125259312507925865235543189173088893915032765084532165 : Int)) * (48247036248326252441749211456640095925133370949144318088379759940444732083551 : Int) =
        (1 : Int) + (30161824408611083301623859610971704742915976008244041850889100701692585761333 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36237182653660276449462006808171555654119938756498077708073758651832832581388 : Int) * ((2 : Int) * (16390246766700321050481125259312507925865235543189173088893915032765084532165 : Int)) =
        (3 : Int) * (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) + (-40964 : Int) * (-40964 : Int) + (-4871096879549238735361867701909905217547717652514063722729459165574414129700 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int) =
        (36237182653660276449462006808171555654119938756498077708073758651832832581388 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) - (21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) + (-25042652616917575661886948779961561988411424584774377117897125955901165135011 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43208462230955820829943285945607605018670933806571005865504367515923698639806 : Int) =
        (36237182653660276449462006808171555654119938756498077708073758651832832581388 : Int) * ((21933938387720517397777775700475712951098354028738066484391338187786808861578 : Int) - (34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int)) - (16390246766700321050481125259312507925865235543189173088893915032765084532165 : Int) + (8428073836811279719660673722252726175627034737648090446113381884727845771927 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((115 : Nat) • base) + ((115 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (50050280728561316283889586560096540338956349451231111423753647685417687456492 : Int) =
        (1 : Int) + (-5298162558167221572098068177101642772190291641728156490580154309799337196057 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (46123018585099466238203170774973770487550977712485997628606620849870381545934 : Int) * ((34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (43208462230955820829943285945607605018670933806571005865504367515923698639806 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-4882435154809753498837801930745037130536156434247287560944235869288155459280 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) =
        (46123018585099466238203170774973770487550977712485997628606620849870381545934 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-40570179029081327776055360147708977561683520100447599705376046939736520168404 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (36612701123945719380912906697697377473105333689555289375180417076038791909164 : Int) =
        (46123018585099466238203170774973770487550977712485997628606620849870381545934 : Int) * ((34129517494893296877003897096003292625773952744021646161908021957385756966113 : Int) - (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int)) - (43208462230955820829943285945607605018670933806571005865504367515923698639806 : Int) + (-13821532817787261768348175303114325936386333216358057077519469485754049949676 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (231 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (231 : Nat) = 115 + 115 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep007
