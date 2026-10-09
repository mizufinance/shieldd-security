import ShielddSecurity.ConcretePointTraceStep087
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep088
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45774878971391228692067467495918152112664540199492981028025739173355321092830
def inputY : F := 52035506119804262380316916469875473567529572518009477012579152597609649711911
def doubleX : F := 28175284432758235473716657307710878332406389077251843513031922229973835423918
def doubleY : F := 49877747558402224044475565124054595491095005357749711091665460176613971249038
def doubleSlope : F := 25801006484223917314053522586765200698367183725027667563797204396919759158755
def outX : F := 28175284432758235473716657307710878332406389077251843513031922229973835423918
def outY : F := 49877747558402224044475565124054595491095005357749711091665460176613971249038

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((280297513421753422205842352 : Nat) • base) + ((280297513421753422205842352 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep087.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (52035506119804262380316916469875473567529572518009477012579152597609649711911 : Int)) * (40612330920583607663403263997710661934139341511462327059573855367925829745064 : Int) =
        (1 : Int) + (80604478788599085517009812800819855979969250941246130723433156702109157032239 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (25801006484223917314053522586765200698367183725027667563797204396919759158755 : Int) * ((2 : Int) * (52035506119804262380316916469875473567529572518009477012579152597609649711911 : Int)) =
        (3 : Int) * (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) + (-40964 : Int) * (-40964 : Int) + (-68672102084620021920147726920247441573882335860654235189858122449651115490962 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int) =
        (25801006484223917314053522586765200698367183725027667563797204396919759158755 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) - (45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) + (-12695352816667517245093949997664699463310699935041858640571530359253474689255 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (49877747558402224044475565124054595491095005357749711091665460176613971249038 : Int) =
        (25801006484223917314053522586765200698367183725027667563797204396919759158755 : Int) * ((45774878971391228692067467495918152112664540199492981028025739173355321092830 : Int) - (28175284432758235473716657307710878332406389077251843513031922229973835423918 : Int)) - (52035506119804262380316916469875473567529572518009477012579152597609649711911 : Int) + (-8659858375480788545457276701205427510169456910976462512386751544004174595547 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (560595026843506844411684704 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (560595026843506844411684704 : Nat) = 280297513421753422205842352 + 280297513421753422205842352 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep088
