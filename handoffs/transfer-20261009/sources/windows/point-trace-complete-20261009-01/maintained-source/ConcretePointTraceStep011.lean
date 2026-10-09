import ShielddSecurity.ConcretePointTraceStep010
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep011
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 22442234978684825731632329529465228058157583984752797698598611937614349975524
def inputY : F := 21746960631068035749333477086487225234479290840653100761459625256678398636989
def doubleX : F := 27471539065225242608588042526815451679189789541666525563133022198926009295444
def doubleY : F := 36243641566637761751694387145438699430928716944987304624160194866414428205103
def doubleSlope : F := 27535936466103341206679984596113178015750894921898560948820163491175332641765
def addX : F := 10333346777456882902386196603700873278109877246905663873291420660941068575558
def addY : F := 38282350565661677357258825406497303688287425657349814821184155678355197368099
def addSlope : F := 21649320867081383582169811066633799241457007243072549221479197746531120706654
def outX : F := 10333346777456882902386196603700873278109877246905663873291420660941068575558
def outY : F := 38282350565661677357258825406497303688287425657349814821184155678355197368099

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1854 : Nat) • base) + ((1854 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep010.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21746960631068035749333477086487225234479290840653100761459625256678398636989 : Int)) * (27630490273584518000301413056292050750919623643537719671355387538388325175347 : Int) =
        (1 : Int) + (22918628980251581618585197391232653496429472625281481408473864488579461430605 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (27535936466103341206679984596113178015750894921898560948820163491175332641765 : Int) * ((2 : Int) * (21746960631068035749333477086487225234479290840653100761459625256678398636989 : Int)) =
        (3 : Int) * (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) + (-40964 : Int) * (-40964 : Int) + (-5975219807683508831415451774185851914950149954247346480174640690565132049630 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int) =
        (27535936466103341206679984596113178015750894921898560948820163491175332641765 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) - (22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) + (-14460096156170526555765124641437328922918419449212945397392776773778160302277 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36243641566637761751694387145438699430928716944987304624160194866414428205103 : Int) =
        (27535936466103341206679984596113178015750894921898560948820163491175332641765 : Int) * ((22442234978684825731632329529465228058157583984752797698598611937614349975524 : Int) - (27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int)) - (21746960631068035749333477086487225234479290840653100761459625256678398636989 : Int) + (2641065822457831073202476059038366615857726838041864797101969574794367238684 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1854 : Nat) • base) + ((1854 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (25503728652211792226129602586616190250035706020014210697956553397419808615054 : Int) =
        (1 : Int) + (-5938046549179203410285311125106799906253835852162874526185029957457252759539 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (21649320867081383582169811066633799241457007243072549221479197746531120706654 : Int) * ((27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (36243641566637761751694387145438699430928716944987304624160194866414428205103 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-5040622758339185802945094921964442773112398272463838698267805715323638918951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int) =
        (21649320867081383582169811066633799241457007243072549221479197746531120706654 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-8938405098427299943154580023550581438870967236893694138666424439564471379423 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (38282350565661677357258825406497303688287425657349814821184155678355197368099 : Int) =
        (21649320867081383582169811066633799241457007243072549221479197746531120706654 : Int) * ((27471539065225242608588042526815451679189789541666525563133022198926009295444 : Int) - (10333346777456882902386196603700873278109877246905663873291420660941068575558 : Int)) - (36243641566637761751694387145438699430928716944987304624160194866414428205103 : Int) + (-7075885024908309386414679289644369216633568138214169408747009177492927559634 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3709 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3709 : Nat) = 1854 + 1854 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep011
