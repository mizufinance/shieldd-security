import ShielddSecurity.ConcretePointTraceStep166
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep167
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31520101102725783935204193735625748357051036600606356108215295550034030650280
def inputY : F := 12290879451489358854826872957033580560610287401604831589909675361892845287554
def doubleX : F := 27392514126270265600367489278637457309884917413997584871806172929801153740431
def doubleY : F := 28603367822327098179148450697288024183981831408632584755694247451151840842448
def doubleSlope : F := 36304384766918309017385716673468342905259771148434235375005149527415644463629
def outX : F := 27392514126270265600367489278637457309884917413997584871806172929801153740431
def outY : F := 28603367822327098179148450697288024183981831408632584755694247451151840842448

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((169429450574667888851428174206284902368378404249190 : Nat) • base) + ((169429450574667888851428174206284902368378404249190 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep166.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (12290879451489358854826872957033580560610287401604831589909675361892845287554 : Int)) * (29731735740449014147907443210276683530610635246971514781250434022965778542451 : Int) =
        (1 : Int) + (13938136005127413824084715916411262213870130255303408616620184150468793204939 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36304384766918309017385716673468342905259771148434235375005149527415644463629 : Int) * ((2 : Int) * (12290879451489358854826872957033580560610287401604831589909675361892845287554 : Int)) =
        (3 : Int) * (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) + (-40964 : Int) * (-40964 : Int) + (-39822443701813950813699840346489800714800083588116007906177871953814980074268 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) =
        (36304384766918309017385716673468342905259771148434235375005149527415644463629 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) - (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) + (-25135622298713321443676432794957534179689406243647344556164548513156140658386 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (28603367822327098179148450697288024183981831408632584755694247451151840842448 : Int) =
        (36304384766918309017385716673468342905259771148434235375005149527415644463629 : Int) * ((31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) - (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int)) - (12290879451489358854826872957033580560610287401604831589909675361892845287554 : Int) + (-2857766848587771242127058469232061050039382526938733213542635648278103582963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (338858901149335777702856348412569804736756808498380 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (338858901149335777702856348412569804736756808498380 : Nat) = 169429450574667888851428174206284902368378404249190 + 169429450574667888851428174206284902368378404249190 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep167
