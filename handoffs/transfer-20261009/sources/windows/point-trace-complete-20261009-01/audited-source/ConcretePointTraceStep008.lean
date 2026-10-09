import ShielddSecurity.ConcretePointTraceStep007
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep008
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18416231769129038938590376633805459194750870281549264888420309157482590710276
def inputY : F := 36612701123945719380912906697697377473105333689555289375180417076038791909164
def doubleX : F := 29184383732484452475154086430322287868723389800109301647765553745042132608699
def doubleY : F := 25666884125835946412107434347323490676169551374671716633505844678230108154117
def doubleSlope : F := 40838626471433315617927927659916569893079092817860756534783940616980206675123
def addX : F := 25086419878455168332628307760170701926943674741615533051579194352381285095965
def addY : F := 20495360833676557890588252262014143857305950680061967017112910574000081292885
def addSlope : F := 45752683813350470398158266975749075061223950391896256639472490979368716313944
def outX : F := 25086419878455168332628307760170701926943674741615533051579194352381285095965
def outY : F := 20495360833676557890588252262014143857305950680061967017112910574000081292885

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((231 : Nat) • base) + ((231 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep007.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36612701123945719380912906697697377473105333689555289375180417076038791909164 : Int)) * (52224608489281997246472372314202810158153245823676635654206498874130460443309 : Int) =
        (1 : Int) + (72930373548535268785329600314300761655784912570436549292639262347645802033527 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40838626471433315617927927659916569893079092817860756534783940616980206675123 : Int) * ((2 : Int) * (36612701123945719380912906697697377473105333689555289375180417076038791909164 : Int)) =
        (3 : Int) * (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) + (-40964 : Int) * (-40964 : Int) + (37625996825836535848607642421150271645016888681906320722554557072264782661512 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int) =
        (40838626471433315617927927659916569893079092817860756534783940616980206675123 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) - (18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) + (-31806342632846888219103479125970898877180355129369104975827700556362169784942 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (25666884125835946412107434347323490676169551374671716633505844678230108154117 : Int) =
        (40838626471433315617927927659916569893079092817860756534783940616980206675123 : Int) * ((18416231769129038938590376633805459194750870281549264888420309157482590710276 : Int) - (29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int)) - (36612701123945719380912906697697377473105333689555289375180417076038791909164 : Int) + (8386558522202537412241681945535189411370096329491882783949802037108015736870 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((231 : Nat) • base) + ((231 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (51908148744367847375361556345408314965985912213143386701419240203197050480762 : Int) =
        (1 : Int) + (-10390195346175828924455540632617798746702934920277060202624176729763754961393 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (45752683813350470398158266975749075061223950391896256639472490979368716313944 : Int) * ((29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (25666884125835946412107434347323490676169551374671716633505844678230108154117 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-9158086618993669601278971364789449702997443080667470960626878565470337938459 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int) =
        (45752683813350470398158266975749075061223950391896256639472490979368716313944 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-39921295661284525402315899178168487903732781498695835686307743046118497117789 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (20495360833676557890588252262014143857305950680061967017112910574000081292885 : Int) =
        (45752683813350470398158266975749075061223950391896256639472490979368716313944 : Int) * ((29184383732484452475154086430322287868723389800109301647765553745042132608699 : Int) - (25086419878455168332628307760170701926943674741615533051579194352381285095965 : Int)) - (25666884125835946412107434347323490676169551374671716633505844678230108154117 : Int) + (-3575659677000703826438879235889127181108359470646741413110568187837811438838 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (463 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (463 : Nat) = 231 + 231 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep008
