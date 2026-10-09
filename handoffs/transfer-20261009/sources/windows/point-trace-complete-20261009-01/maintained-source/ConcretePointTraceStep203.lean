import ShielddSecurity.ConcretePointTraceStep202
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep203
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10130666718819175285113361282515029354779409130751530781402943239498125319793
def inputY : F := 13733683658468600921724714767127161246474265720849013178763607005477553543462
def doubleX : F := 33851810951064585500825446279737278432789666884793734748885072359512399705659
def doubleY : F := 25275900908920545139126579851950304273789888972456187893262919421567867729811
def doubleSlope : F := 19603783758714800123655640292808235483954509904608331706422245439708521890727
def addX : F := 22654833802152741492955822644190109173062412335261798635205989424837512510783
def addY : F := 3317576814041047444775866956284789662008526847095044842404141569430213747165
def addSlope : F := 5892815383210664309896449737161043178644635713071958920820981477190889021103
def outX : F := 22654833802152741492955822644190109173062412335261798635205989424837512510783
def outY : F := 3317576814041047444775866956284789662008526847095044842404141569430213747165

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((11643103187159151818851952177743750613291811052847033070217291 : Nat) • base) + ((11643103187159151818851952177743750613291811052847033070217291 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep202.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (13733683658468600921724714767127161246474265720849013178763607005477553543462 : Int)) * (30464163684716136180241583070598411499188039635303988535707052881597721564183 : Int) =
        (1 : Int) + (15957974786093258975154729261073966404539028782393778928464758164862130615507 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19603783758714800123655640292808235483954509904608331706422245439708521890727 : Int) * ((2 : Int) * (13733683658468600921724714767127161246474265720849013178763607005477553543462 : Int)) =
        (3 : Int) * (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) + (-40964 : Int) * (-40964 : Int) + (4397239562207820406307768431824502878771603166216264511572007325029915300081 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int) =
        (19603783758714800123655640292808235483954509904608331706422245439708521890727 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) - (10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) + (-7329110773395712903170099505853018721001622600976075380366024484105706890204 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25275900908920545139126579851950304273789888972456187893262919421567867729811 : Int) =
        (19603783758714800123655640292808235483954509904608331706422245439708521890727 : Int) * ((10130666718819175285113361282515029354779409130751530781402943239498125319793 : Int) - (33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int)) - (13733683658468600921724714767127161246474265720849013178763607005477553543462 : Int) + (8868435598435774889251061805430127755820014633870564213717547821355683902335 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((11643103187159151818851952177743750613291811052847033070217291 : Nat) • base) + ((11643103187159151818851952177743750613291811052847033070217291 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (18170253928339740350719506817083298868906913859249093364125949209871910024163 : Int) =
        (1 : Int) + (-2019676731997563119335224554678918563499295576198651521985862707780566456201 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (5892815383210664309896449737161043178644635713071958920820981477190889021103 : Int) * ((33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (25275900908920545139126579851950304273789888972456187893262919421567867729811 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-655003620883098916327422311188190247891144653572348168950655780778200850449 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int) =
        (5892815383210664309896449737161043178644635713071958920820981477190889021103 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-662242653996490290162103211457359551909423022637159087754086947581855211804 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (3317576814041047444775866956284789662008526847095044842404141569430213747165 : Int) =
        (5892815383210664309896449737161043178644635713071958920820981477190889021103 : Int) * ((33851810951064585500825446279737278432789666884793734748885072359512399705659 : Int) - (22654833802152741492955822644190109173062412335261798635205989424837512510783 : Int)) - (25275900908920545139126579851950304273789888972456187893262919421567867729811 : Int) + (-1258331609193117850452736260270265370765867369086954678139677696644103496404 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (23286206374318303637703904355487501226583622105694066140434583 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (23286206374318303637703904355487501226583622105694066140434583 : Nat) = 11643103187159151818851952177743750613291811052847033070217291 + 11643103187159151818851952177743750613291811052847033070217291 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep203
