import ShielddSecurity.ConcretePointTraceStep073
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep074
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 34253846517722219294123708534716221629448590821177048022499316921823396196802
def inputY : F := 28965364953740762307463463105675419620314025364945790956642152856696220347478
def doubleX : F := 2478645524739292913243383111707391783150337075550053005530687454704087342815
def doubleY : F := 34200116096909579546620736230181066166885862008073870386574736499778318998189
def doubleSlope : F := 39726983014501735775926666829100102027836137013737619854889439547953118368316
def addX : F := 14090428345326626357970098522365631802949072654850059508085601349138350972482
def addY : F := 15622441200651738356359453288114531138497638458394178828472229200618406159507
def addSlope : F := 33775553796195773566970322421632424091516986225106057446284732316665988488220
def outX : F := 14090428345326626357970098522365631802949072654850059508085601349138350972482
def outY : F := 15622441200651738356359453288114531138497638458394178828472229200618406159507

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((17108002528183192273305 : Nat) • base) + ((17108002528183192273305 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep073.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28965364953740762307463463105675419620314025364945790956642152856696220347478 : Int)) * (4734679651054013285623077813915678412361890791966825503461903165975637779055 : Int) =
        (1 : Int) + (5230835704517233408570278811433130231234398131161221565250741580099602664083 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (39726983014501735775926666829100102027836137013737619854889439547953118368316 : Int) * ((2 : Int) * (28965364953740762307463463105675419620314025364945790956642152856696220347478 : Int)) =
        (3 : Int) * (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) + (-40964 : Int) * (-40964 : Int) + (-23239144510452485807677944105669655104991149540810236802934923551989772945580 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int) =
        (39726983014501735775926666829100102027836137013737619854889439547953118368316 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) - (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) + (-30098347251066193282461309081462628655033177305183427116507037192430949186485 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34200116096909579546620736230181066166885862008073870386574736499778318998189 : Int) =
        (39726983014501735775926666829100102027836137013737619854889439547953118368316 : Int) * ((34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) - (2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int)) - (28965364953740762307463463105675419620314025364945790956642152856696220347478 : Int) + (-24073840017252530108777000438853230312639552845364937219433245717167374539825 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((17108002528183192273305 : Nat) • base) + ((17108002528183192273305 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (44669323519071812277588435430990495639601755957080574703157124741255558899353 : Int) =
        (1 : Int) + (-31691447469163045042737659246440329559706773951958272793898517513959570104085 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (33775553796195773566970322421632424091516986225106057446284732316665988488220 : Int) * ((2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34200116096909579546620736230181066166885862008073870386574736499778318998189 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-23962668438822838060538912480475837647148177578468481228169445623864881767731 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int) =
        (33775553796195773566970322421632424091516986225106057446284732316665988488220 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-21755869057771845368172930527548277583119809916529536072579757244241794907876 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15622441200651738356359453288114531138497638458394178828472229200618406159507 : Int) =
        (33775553796195773566970322421632424091516986225106057446284732316665988488220 : Int) * ((2478645524739292913243383111707391783150337075550053005530687454704087342815 : Int) - (14090428345326626357970098522365631802949072654850059508085601349138350972482 : Int)) - (34200116096909579546620736230181066166885862008073870386574736499778318998189 : Int) + (7479505091058977159271867044307191168140167289785105303048587204242719703572 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (34216005056366384546611 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (34216005056366384546611 : Nat) = 17108002528183192273305 + 17108002528183192273305 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep074
