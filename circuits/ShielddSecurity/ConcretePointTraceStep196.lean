import ShielddSecurity.ConcretePointTraceStep195
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep196
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 45291916205121456350242883724662810644790040143665673920277142435155623198101
def inputY : F := 41003502079105349511337519576762210108166022459189333537549067628848645574648
def doubleX : F := 13037732646876030161357549737001859368074467920000012285644500192185399332167
def doubleY : F := 45711054769881049082440326147553800403594010491525163736076675241833055830425
def doubleSlope : F := 37464590623525816897892528199006214551238557468385405443281206434162095924555
def addX : F := 25504733354073767449612356242116994149889995602194937066522614093910767300898
def addY : F := 15552006826525393596728363244627764074434026645562725053557010621546071563880
def addSlope : F := 29222073265395529065265776512988647614567128602893066863274200456262844739021
def outX : F := 25504733354073767449612356242116994149889995602194937066522614093910767300898
def outY : F := 15552006826525393596728363244627764074434026645562725053557010621546071563880

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((90961743649680873584780876388623051666342273850367445861072 : Nat) • base) + ((90961743649680873584780876388623051666342273850367445861072 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep195.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (41003502079105349511337519576762210108166022459189333537549067628848645574648 : Int)) * (21135347130295664305469801619689893856035800814727072574476742139086430768100 : Int) =
        (1 : Int) + (33054592761361533478854139649303628213994467490063496144694899525792560562623 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (37464590623525816897892528199006214551238557468385405443281206434162095924555 : Int) * ((2 : Int) * (41003502079105349511337519576762210108166022459189333537549067628848645574648 : Int)) =
        (3 : Int) * (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) + (-40964 : Int) * (-40964 : Int) + (-58771102251153971817650268354906737604229341367135801936867131208080474875291 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int) =
        (37464590623525816897892528199006214551238557468385405443281206434162095924555 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) - (45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) + (-26767848269922591411514651069653890661054093304101371773882222841673558440848 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (45711054769881049082440326147553800403594010491525163736076675241833055830425 : Int) =
        (37464590623525816897892528199006214551238557468385405443281206434162095924555 : Int) * ((45291916205121456350242883724662810644790040143665673920277142435155623198101 : Int) - (13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int)) - (41003502079105349511337519576762210108166022459189333537549067628848645574648 : Int) + (-23045096107768245928673896192748513721126414515800852646185169401384816663369 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((90961743649680873584780876388623051666342273850367445861072 : Nat) • base) + ((90961743649680873584780876388623051666342273850367445861072 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (20471711538003702542659354473808331232646904553348921466178722946079069676895 : Int) =
        (1 : Int) + (-10401602697363157545748790116448113102674092831312989809659383076569146625717 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (29222073265395529065265776512988647614567128602893066863274200456262844739021 : Int) * ((13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (45711054769881049082440326147553800403594010491525163736076675241833055830425 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-14847629888474006609593835412808996101963732790163045388338112965074945342155 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int) =
        (29222073265395529065265776512988647614567128602893066863274200456262844739021 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-16285216239381458547902757365353604917216441779619391192993182518929695625397 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15552006826525393596728363244627764074434026645562725053557010621546071563880 : Int) =
        (29222073265395529065265776512988647614567128602893066863274200456262844739021 : Int) * ((13037732646876030161357549737001859368074467920000012285644500192185399332167 : Int) - (25504733354073767449612356242116994149889995602194937066522614093910767300898 : Int)) - (45711054769881049082440326147553800403594010491525163736076675241833055830425 : Int) + (6947754888208431861947304108920161255726774638423429985263355666254834652512 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (181923487299361747169561752777246103332684547700734891722145 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (181923487299361747169561752777246103332684547700734891722145 : Nat) = 90961743649680873584780876388623051666342273850367445861072 + 90961743649680873584780876388623051666342273850367445861072 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep196
