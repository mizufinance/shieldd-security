import ShielddSecurity.ConcretePointTraceStep123
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep124
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4943177486272274119331879730300113294250427351211954246019216143541079443262
def inputY : F := 32362558564332938204842363969659599991755105398382129018648785744185269053974
def doubleX : F := 8388882975817773826672242512768139365344358479145769439428569020000064898335
def doubleY : F := 14024000315839213583065597442988917516460114968182416468150198087281919517762
def doubleSlope : F := 20920153944660444603925753234774572942421377302671828223194714215689875486665
def addX : F := 26212138188597492976639860102692701785350744286201968816696184634559745205319
def addY : F := 1185202506295424070920956967281498296060393024609547071503116731031146342752
def addSlope : F := 40476250337184991850780451043399266480163842572036794613962464564194683194198
def outX : F := 26212138188597492976639860102692701785350744286201968816696184634559745205319
def outY : F := 1185202506295424070920956967281498296060393024609547071503116731031146342752

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((19261898452744832053602769315862690560 : Nat) • base) + ((19261898452744832053602769315862690560 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep123.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (32362558564332938204842363969659599991755105398382129018648785744185269053974 : Int)) * (13368339641562877317763149576427665474136038931899375526237892825673160574336 : Int) =
        (1 : Int) + (16501438113240418686037449471913716149625419559794547456958671677493564142079 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (20920153944660444603925753234774572942421377302671828223194714215689875486665 : Int) * ((2 : Int) * (32362558564332938204842363969659599991755105398382129018648785744185269053974 : Int)) =
        (3 : Int) * (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) + (-40964 : Int) * (-40964 : Int) + (24425155471478583664707707557066073758844899502151765013960675324967815488848 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int) =
        (20920153944660444603925753234774572942421377302671828223194714215689875486665 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) - (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) + (-8346439143174627475844343455926748945195458084745969683686910633844351379518 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (14024000315839213583065597442988917516460114968182416468150198087281919517762 : Int) =
        (20920153944660444603925753234774572942421377302671828223194714215689875486665 : Int) * ((4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) - (8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int)) - (32362558564332938204842363969659599991755105398382129018648785744185269053974 : Int) + (1374720819448589615114438665111840692661880343693865349884517951600585915137 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((19261898452744832053602769315862690560 : Nat) • base) + ((19261898452744832053602769315862690560 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (40331526115963010603814478313695773508936283998632181411294468619416771855755 : Int) =
        (1 : Int) + (-24068007394496076267258362279032153866561165059551813462132794573173668082557 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (40476250337184991850780451043399266480163842572036794613962464564194683194198 : Int) * ((8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (14024000315839213583065597442988917516460114968182416468150198087281919517762 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-24154372180607026049103259660500840850583038340938324958999087450988301319440 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int) =
        (40476250337184991850780451043399266480163842572036794613962464564194683194198 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-31244388233947797785807242943041900808821172053347205970992164902397546311795 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (1185202506295424070920956967281498296060393024609547071503116731031146342752 : Int) =
        (40476250337184991850780451043399266480163842572036794613962464564194683194198 : Int) * ((8388882975817773826672242512768139365344358479145769439428569020000064898335 : Int) - (26212138188597492976639860102692701785350744286201968816696184634559745205319 : Int)) - (14024000315839213583065597442988917516460114968182416468150198087281919517762 : Int) + (13758110023082553201979221574237324195067155840030497446595926589863872314642 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (38523796905489664107205538631725381121 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (38523796905489664107205538631725381121 : Nat) = 19261898452744832053602769315862690560 + 19261898452744832053602769315862690560 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep124
