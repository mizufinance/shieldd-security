import ShielddSecurity.ConcretePointTraceStep013
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep014
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44458785688534054192797513222025200578002196316154071113948646250915212113101
def inputY : F := 46054047493182044412507592300112323905490616910150683491789173610876730800645
def doubleX : F := 37006962985838004545856200880733590356295919967624653078461303533725100341689
def doubleY : F := 22873181554367930158109166597368488836153278721529420334005121869968971097870
def doubleSlope : F := 39654732237277002705531755753612734968721626269572917737552082517005022101149
def addX : F := 16563918511737849350055151229619595918806303779926919627409058753629890695841
def addY : F := 7830866387738348311722657341583576969185386966220487808300292672582758839180
def addSlope : F := 42049831346530449690002730609043259465208739991193180679733111944263675109491
def outX : F := 16563918511737849350055151229619595918806303779926919627409058753629890695841
def outY : F := 7830866387738348311722657341583576969185386966220487808300292672582758839180

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((14838 : Nat) • base) + ((14838 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep013.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (46054047493182044412507592300112323905490616910150683491789173610876730800645 : Int)) * (18773428486146668679330507070097044943064711802758439748325338974191349657667 : Int) =
        (1 : Int) + (32977131180638282144735414510236741194185568131083633133173879100834579365533 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (39654732237277002705531755753612734968721626269572917737552082517005022101149 : Int) * ((2 : Int) * (46054047493182044412507592300112323905490616910150683491789173610876730800645 : Int)) =
        (3 : Int) * (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) + (-40964 : Int) * (-40964 : Int) + (-43428836145511643970323245635893635440809172437297939959974145510062780342681 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int) =
        (39654732237277002705531755753612734968721626269572917737552082517005022101149 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) - (44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) + (-29988968116929148558600959855697642889553668031211585177098683546918646270206 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (22873181554367930158109166597368488836153278721529420334005121869968971097870 : Int) =
        (39654732237277002705531755753612734968721626269572917737552082517005022101149 : Int) * ((44458785688534054192797513222025200578002196316154071113948646250915212113101 : Int) - (37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int)) - (46054047493182044412507592300112323905490616910150683491789173610876730800645 : Int) + (-5635455362729388086021904205043341225596768495373339308674295211803835740721 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((14838 : Nat) • base) + ((14838 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (16468008088593610134444607281974858023325280198552605775544605291001942611859 : Int) =
        (1 : Int) + (-839560265554365562326916445909259583111317111885820262129267556473845407919 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (42049831346530449690002730609043259465208739991193180679733111944263675109491 : Int) * ((37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (22873181554367930158109166597368488836153278721529420334005121869968971097870 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2143754568365914876816599210145622339678337323432355087762497373660199418706 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int) =
        (42049831346530449690002730609043259465208739991193180679733111944263675109491 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-33720965090526870317815247173075835596805524351695083852099462935735193698372 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (7830866387738348311722657341583576969185386966220487808300292672582758839180 : Int) =
        (42049831346530449690002730609043259465208739991193180679733111944263675109491 : Int) * ((37006962985838004545856200880733590356295919967624653078461303533725100341689 : Int) - (16563918511737849350055151229619595918806303779926919627409058753629890695841 : Int)) - (22873181554367930158109166597368488836153278721529420334005121869968971097870 : Int) + (-16393863351656436775082622421501522520655241602189053269332202923118933341486 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (29677 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (29677 : Nat) = 14838 + 14838 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep014
