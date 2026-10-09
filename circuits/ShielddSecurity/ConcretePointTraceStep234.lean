import ShielddSecurity.ConcretePointTraceStep233
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep234
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18143046994782760015854533110955317951507927011319605942362129618854640247793
def inputY : F := 31536867008158413901505252924368009717278825650594881510413103991050827413766
def doubleX : F := 51879303690389523702613670557382265534063768593782947271136965892745830724673
def doubleY : F := 39701221710512691522667763078228116030368239440699146637725301958117755370622
def doubleSlope : F := 10783922110518619606603168409486456989232119436608093363286472333124930812215
def addX : F := 18062882933548936926588002041462018784690172313961547866306186535222960580237
def addY : F := 50525598120800224671539119945708881396506916521010517965741169178716074463038
def addSlope : F := 14133171519140515585959145887079838031183912230897407057201168358162021184966
def outX : F := 18062882933548936926588002041462018784690172313961547866306186535222960580237
def outY : F := 50525598120800224671539119945708881396506916521010517965741169178716074463038

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) • base) + ((25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep233.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (31536867008158413901505252924368009717278825650594881510413103991050827413766 : Int)) * (45573189721823127285926987917670950366051492633895984520240605149449444064768 : Int) =
        (1 : Int) + (54818790326073702367105091496085697717929602031299775465943398436092426315775 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10783922110518619606603168409486456989232119436608093363286472333124930812215 : Int) * ((2 : Int) * (31536867008158413901505252924368009717278825650594881510413103991050827413766 : Int)) =
        (3 : Int) * (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) + (-40964 : Int) * (-40964 : Int) + (-5861029817596025224168545343418556227811792845505063577685845087673578090255 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int) =
        (10783922110518619606603168409486456989232119436608093363286472333124930812215 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) - (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) + (-2217813199404704931082813358831524301459154094332903728341007728435341921718 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (39701221710512691522667763078228116030368239440699146637725301958117755370622 : Int) =
        (10783922110518619606603168409486456989232119436608093363286472333124930812215 : Int) * ((18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) - (51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int)) - (31536867008158413901505252924368009717278825650594881510413103991050827413766 : Int) + (6938172830925961018002599372019209784463279863829764973807095419252460996276 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) • base) + ((25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (758832484253313564158636797786710845594312460925897924920587262578852190394 : Int) =
        (1 : Int) + (176540726011005375510052227114502583129143775050145691834673065324838740843 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (14133171519140515585959145887079838031183912230897407057201168358162021184966 : Int) * ((51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (39701221710512691522667763078228116030368239440699146637725301958117755370622 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (3288051595843678073743353383696186611685592732732531613661505302503934641728 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int) =
        (14133171519140515585959145887079838031183912230897407057201168358162021184966 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-3809348781198518931115436111731180172110861210672268361977066166749315437387 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (50525598120800224671539119945708881396506916521010517965741169178716074463038 : Int) =
        (14133171519140515585959145887079838031183912230897407057201168358162021184966 : Int) * ((51879303690389523702613670557382265534063768593782947271136965892745830724673 : Int) - (18062882933548936926588002041462018784690172313961547866306186535222960580237 : Int)) - (39701221710512691522667763078228116030368239440699146637725301958117755370622 : Int) + (-9114623778541736924089825320302368834526352309138276267593789786428853604732 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (50006747412801924209068050869165387952468271376589334727213738726747003 : Nat) = 25003373706400962104534025434582693976234135688294667363606869363373501 + 25003373706400962104534025434582693976234135688294667363606869363373501 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep234
