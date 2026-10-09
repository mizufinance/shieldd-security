import ShielddSecurity.ConcretePointTraceStep150
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep151
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26743128294051169123626303766926877689760850029753659611217365217079061734238
def inputY : F := 3582510313114024221961480449621450297679357366172301452415825860858443750120
def doubleX : F := 6775314967478125008149641610255088680195636438869901274864264864834858508636
def doubleY : F := 36949095376739038850586615509460425015126621042281184187047335677709398213334
def doubleSlope : F := 6193692302076189717887428484787752519232455871958631702260167752875983077553
def addX : F := 8546699611385590940827842050899672520723875975458564781221614448166593430857
def addY : F := 36560873442994454358221483337331433721597935770518524736843426816175207837731
def addSlope : F := 15845348685781759224054390792074778827369930432597022230239851679171849661600
def outX : F := 8546699611385590940827842050899672520723875975458564781221614448166593430857
def outY : F := 36560873442994454358221483337331433721597935770518524736843426816175207837731

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2585288247294126721976137912083204687017492740 : Nat) • base) + ((2585288247294126721976137912083204687017492740 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep150.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3582510313114024221961480449621450297679357366172301452415825860858443750120 : Int)) * (50950314551876808389531605009291646272425151403910865441995198650750863256226 : Int) =
        (1 : Int) + (6962028448228829955161969592852206747164758409478706358994886897492437183903 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (6193692302076189717887428484787752519232455871958631702260167752875983077553 : Int) * ((2 : Int) * (3582510313114024221961480449621450297679357366172301452415825860858443750120 : Int)) =
        (3 : Int) * (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) + (-40964 : Int) * (-40964 : Int) + (-40071931530497204213755691714075258766716493128366412346847665126808730835180 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int) =
        (6193692302076189717887428484787752519232455871958631702260167752875983077553 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) - (26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) + (-731595004463573925997179842814825117344416120921961283047350938109618983505 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36949095376739038850586615509460425015126621042281184187047335677709398213334 : Int) =
        (6193692302076189717887428484787752519232455871958631702260167752875983077553 : Int) * ((26743128294051169123626303766926877689760850029753659611217365217079061734238 : Int) - (6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int)) - (3582510313114024221961480449621450297679357366172301452415825860858443750120 : Int) + (-2358585439396972674166845788708745875783421165499623621553244489978323600804 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2585288247294126721976137912083204687017492740 : Nat) • base) + ((2585288247294126721976137912083204687017492740 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (13084940841600049461031545585140007217841994141375084423149974083843265671782 : Int) =
        (1 : Int) + (-8211145945400859081660635227964808179039203524972478133649943838256507520235 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (15845348685781759224054390792074778827369930432597022230239851679171849661600 : Int) * ((6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (36949095376739038850586615509460425015126621042281184187047335677709398213334 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-9943374768732223927333470664626552169234341787455193643821993829022157028876 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) =
        (15845348685781759224054390792074778827369930432597022230239851679171849661600 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4788230846447419766272742681168197416002053974761491130908865441111571387984 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (36560873442994454358221483337331433721597935770518524736843426816175207837731 : Int) =
        (15845348685781759224054390792074778827369930432597022230239851679171849661600 : Int) * ((6775314967478125008149641610255088680195636438869901274864264864834858508636 : Int) - (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int)) - (36949095376739038850586615509460425015126621042281184187047335677709398213334 : Int) + (535286332985012618772727181292489296734387038770906633688011463041053991705 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5170576494588253443952275824166409374034985481 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (5170576494588253443952275824166409374034985481 : Nat) = 2585288247294126721976137912083204687017492740 + 2585288247294126721976137912083204687017492740 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep151
