import ShielddSecurity.ConcretePointTraceStep113
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep114
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 1187218077990636939514552056612861490503384585195403608129595451059979682121
def inputY : F := 36685944280296316684503114723197426378612917856270484750074620125437188168126
def doubleX : F := 32698972164611612222203196039459083865397878118951247337795346401591455626716
def doubleY : F := 40507720500101248269687281098611442766368013394016932526751165366490820113747
def doubleSlope : F := 39511309570343880209498655919895153765307359840861657781273545937704983489186
def addX : F := 28242056687444847643758468803987694961131337139329849831101088473582876704369
def addY : F := 16348322006186725381924241635900085310008306328641021847733362873200594801659
def addSlope : F := 49883483153403687269905409009390599847983859014087219800605377955162498421745
def outX : F := 28242056687444847643758468803987694961131337139329849831101088473582876704369
def outY : F := 16348322006186725381924241635900085310008306328641021847733362873200594801659

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((18810447707758625052346454410022158 : Nat) • base) + ((18810447707758625052346454410022158 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep113.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36685944280296316684503114723197426378612917856270484750074620125437188168126 : Int)) * (34275588215602234431430805796627500302853182927566866170243537365465402209080 : Int) =
        (1 : Int) + (47960764085747464850893626115744773312485461423128038109941869409635733075743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (39511309570343880209498655919895153765307359840861657781273545937704983489186 : Int) * ((2 : Int) * (36685944280296316684503114723197426378612917856270484750074620125437188168126 : Int)) =
        (3 : Int) * (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) + (-40964 : Int) * (-40964 : Int) + (55206305467700406769731776434064842494275305953329345218530862565944044457093 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int) =
        (39511309570343880209498655919895153765307359840861657781273545937704983489186 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) - (1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) + (-29772433067048373187032581135101663421106319305146329379554097867381234898462 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (40507720500101248269687281098611442766368013394016932526751165366490820113747 : Int) =
        (39511309570343880209498655919895153765307359840861657781273545937704983489186 : Int) * ((1187218077990636939514552056612861490503384585195403608129595451059979682121 : Int) - (32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int)) - (36685944280296316684503114723197426378612917856270484750074620125437188168126 : Int) + (23744634120489510290368313139716919322842832799014984753750537384699301196311 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((18810447707758625052346454410022158 : Nat) • base) + ((18810447707758625052346454410022158 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12026434035926860304151082567056619915676168050081937334163357179683101554360 : Int) =
        (1 : Int) + (-1601182652948515730281601367788934703266506999535998290642167681334126311817 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (49883483153403687269905409009390599847983859014087219800605377955162498421745 : Int) * ((32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (40507720500101248269687281098611442766368013394016932526751165366490820113747 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-6641417369045074643273428109715206682495372228890156542113357492639320757232 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) =
        (49883483153403687269905409009390599847983859014087219800605377955162498421745 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-47455332502894971743991393613596887563655500128361013261176568134075990674825 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (16348322006186725381924241635900085310008306328641021847733362873200594801659 : Int) =
        (49883483153403687269905409009390599847983859014087219800605377955162498421745 : Int) * ((32698972164611612222203196039459083865397878118951247337795346401591455626716 : Int) - (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int)) - (40507720500101248269687281098611442766368013394016932526751165366490820113747 : Int) + (-4239968673715521968147673818512121982440165702798373635018837210586763350893 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (37620895415517250104692908820044317 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (37620895415517250104692908820044317 : Nat) = 18810447707758625052346454410022158 + 18810447707758625052346454410022158 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep114
