import ShielddSecurity.ConcretePointTraceStep143
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep144
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30587028541489315436923749089162205017728965372456373683571427986941776893865
def inputY : F := 1404480771254171368937995122912530319389805155987308049282722847233343187735
def doubleX : F := 23205563505794635098949225240501162078543634659777595684979708311290565490253
def doubleY : F := 47837759035518536943222766671967722103556233978764527288865151830917372821691
def doubleSlope : F := 43368869130241186732062833681634131623296917019573724378331212531511246592606
def outX : F := 23205563505794635098949225240501162078543634659777595684979708311290565490253
def outY : F := 47837759035518536943222766671967722103556233978764527288865151830917372821691

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((20197564431985365015438577438150036617324162 : Nat) • base) + ((20197564431985365015438577438150036617324162 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep143.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1404480771254171368937995122912530319389805155987308049282722847233343187735 : Int)) * (47329035413833296371999261898926813659928749417720889184564999035794111250939 : Int) =
        (1 : Int) + (2535390891778954913936186639488624229166166767936773259045159220222644759833 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (43368869130241186732062833681634131623296917019573724378331212531511246592606 : Int) * ((2 : Int) * (1404480771254171368937995122912530319389805155987308049282722847233343187735 : Int)) =
        (3 : Int) * (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) + (-40964 : Int) * (-40964 : Int) + (-51203063751634234564886910079027006170644140411705507125254013918371394624847 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int) =
        (43368869130241186732062833681634131623296917019573724378331212531511246592606 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) - (30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) + (-35869694238043401449224813797778533793474603181134386057064261688746169390317 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (47837759035518536943222766671967722103556233978764527288865151830917372821691 : Int) =
        (43368869130241186732062833681634131623296917019573724378331212531511246592606 : Int) * ((30587028541489315436923749089162205017728965372456373683571427986941776893865 : Int) - (23205563505794635098949225240501162078543634659777595684979708311290565490253 : Int)) - (1404480771254171368937995122912530319389805155987308049282722847233343187735 : Int) + (-6105091028867780831896673637250126062793300632619002077963157637609273060342 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (40395128863970730030877154876300073234648324 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (40395128863970730030877154876300073234648324 : Nat) = 20197564431985365015438577438150036617324162 + 20197564431985365015438577438150036617324162 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep144
