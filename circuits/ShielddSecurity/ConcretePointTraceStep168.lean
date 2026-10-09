import ShielddSecurity.ConcretePointTraceStep167
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep168
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 27392514126270265600367489278637457309884917413997584871806172929801153740431
def inputY : F := 28603367822327098179148450697288024183981831408632584755694247451151840842448
def doubleX : F := 984427931365172150694326082322851414800721352246275862403639658460102120385
def doubleY : F := 44037299694460653571958648373567713021466073332498980809467904595161319651603
def doubleSlope : F := 49627268875485743371669670263602784198564446070110328856355380754236240942258
def addX : F := 32813600355130895053914219587385840934503052564880347515933484622823044827327
def addY : F := 32471264338507219449362255029578969297361792534565272293444715920611648997732
def addSlope : F := 18133781670743778253754105147783391437621445250538800545186843198078603683455
def outX : F := 32813600355130895053914219587385840934503052564880347515933484622823044827327
def outY : F := 32471264338507219449362255029578969297361792534565272293444715920611648997732

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((338858901149335777702856348412569804736756808498380 : Nat) • base) + ((338858901149335777702856348412569804736756808498380 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep167.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28603367822327098179148450697288024183981831408632584755694247451151840842448 : Int)) * (10671915828332885974850659962259850234758676204978653907533121999616854057102 : Int) =
        (1 : Int) + (11642896501192439551461676854412549397295146030743439684452647467905616764607 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (49627268875485743371669670263602784198564446070110328856355380754236240942258 : Int) * ((2 : Int) * (28603367822327098179148450697288024183981831408632584755694247451151840842448 : Int)) =
        (3 : Int) * (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) + (-40964 : Int) * (-40964 : Int) + (11213020835232486762170103379910272097937306477354765236249053562007200847485 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (984427931365172150694326082322851414800721352246275862403639658460102120385 : Int) =
        (49627268875485743371669670263602784198564446070110328856355380754236240942258 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) - (27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) + (-46969099072233210729743140624191996503319403664649993816042484502110236523245 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44037299694460653571958648373567713021466073332498980809467904595161319651603 : Int) =
        (49627268875485743371669670263602784198564446070110328856355380754236240942258 : Int) * ((27392514126270265600367489278637457309884917413997584871806172929801153740431 : Int) - (984427931365172150694326082322851414800721352246275862403639658460102120385 : Int)) - (28603367822327098179148450697288024183981831408632584755694247451151840842448 : Int) + (-24993598174999933648475819688187765187380482870368208145944750403477118488409 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((338858901149335777702856348412569804736756808498380 : Nat) • base) + ((338858901149335777702856348412569804736756808498380 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((984427931365172150694326082322851414800721352246275862403639658460102120385 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (17264725700090635116454124633519583601261804824202743146132694379359762423486 : Int) =
        (1 : Int) + (-12740744498340385837010785921361968809095296510711737022957702670745033831133 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (18133781670743778253754105147783391437621445250538800545186843198078603683455 : Int) * ((984427931365172150694326082322851414800721352246275862403639658460102120385 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (44037299694460653571958648373567713021466073332498980809467904595161319651603 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-13382076441238891895616212843323520855425544580423369025862129028367029940119 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int) =
        (18133781670743778253754105147783391437621445250538800545186843198078603683455 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (984427931365172150694326082322851414800721352246275862403639658460102120385 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-6271165239141288967363393755131530115903531363475692640080369140660749021046 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (32471264338507219449362255029578969297361792534565272293444715920611648997732 : Int) =
        (18133781670743778253754105147783391437621445250538800545186843198078603683455 : Int) * ((984427931365172150694326082322851414800721352246275862403639658460102120385 : Int) - (32813600355130895053914219587385840934503052564880347515933484622823044827327 : Int)) - (44037299694460653571958648373567713021466073332498980809467904595161319651603 : Int) + (11007411654050592549996312443663424917939961681012703845802826583627997446265 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (677717802298671555405712696825139609473513616996761 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (677717802298671555405712696825139609473513616996761 : Nat) = 338858901149335777702856348412569804736756808498380 + 338858901149335777702856348412569804736756808498380 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep168
