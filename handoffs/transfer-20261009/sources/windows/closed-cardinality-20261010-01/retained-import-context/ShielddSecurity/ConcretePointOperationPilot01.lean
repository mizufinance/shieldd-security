import ShielddSecurity.ConcretePointOperationRows01
import ShielddSecurity.ConcreteIntegerCertificates01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointOperationPilot01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def doubleX : F := 28324062100449705322624668797990766441943757807898995800682840219674339513338
def doubleY : F := 12258570448296220020156397120951265589547158368671571358984495645271716598085
def doubleSlope : F := 41910987719626125362350461908700994921492333169185432178402510938758023084178
def addX : F := 21393289750074163033520183963327281622799057116362233550947986343578876885527
def addY : F := 44648599647213915497370463328261413339747416338771684073573383575116587694472
def addSlope : F := 29466273245007724237561535848886413388602629066805410659863680948221898966238

theorem base_valid : curve.Equation baseX baseY := by
  apply (equation_iff baseX baseY).mp
  change baseY * baseY = baseX * baseX * baseX + A * B * baseX * baseX + B * B * baseX
  have integer : (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) * (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) =
        (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (40962 : Int) * (-40964 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-40964 : Int) * (-40964 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1191498259571838000182015081873936015409257214238454722756698597879084578161385511490524065196601621669727011039840539826099278608396156146613873712302799 : Int) * (Scalar.modulus : Int) := by decide +kernel
  have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal

def base : curve.Point := WeierstrassCurve.Affine.Point.mk base_valid

theorem first_double : ∃ output : curve.Equation doubleX doubleY,
    base + base = WeierstrassCurve.Affine.Point.mk output := by
  have nonzero : (2 : F) * baseY ≠ 0 := by
    have integer : ((2 : Int) * (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int)) * (6725489189848799846698049682679194637034190120772140444055125751949150996437 : Int) =
        (1 : Int) + (11041956849300571267766663304334992286625533247626010876571363844141553704931 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have slopeRow : doubleSlope * (2 * baseY) = 3 * baseX ^ 2 + 2 * (A * B) * baseX + B * B := by
    have integer : (41910987719626125362350461908700994921492333169185432178402510938758023084178 : Int) * ((2 : Int) * (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int)) =
        (3 : Int) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-40964 : Int) * (-40964 : Int) + (-21272790600696770432078173040064649622161831729084021395140786563277635900723 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - baseX - baseX := by
    have integer : (28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int) =
        (41910987719626125362350461908700994921492333169185432178402510938758023084178 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-33498647362481533661823142599496201878735541388813111008658941439493983441196 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have yRow : doubleY = doubleSlope * (baseX - doubleX) - baseY := by
    have integer : (12258570448296220020156397120951265589547158368671571358984495645271716598085 : Int) =
        (41910987719626125362350461908700994921492333169185432178402510938758023084178 : Int) * ((39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) - (28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int)) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-9076752018147786379762338657392155173433695438626165803086000873285170249683 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  exact ConcretePointOperationRows01.tangent_rows base_valid nonzero slopeRow xRow yRow

theorem first_add : ∃ output : curve.Equation addX addY,
    (base + base) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := first_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (5044976427016744354829473188350289089516744604033904348189568983080548905912 : Int) =
        (1 : Int) + (-1092601307126644324344762963561233953852410458789846851829713686495490782457 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (29466273245007724237561535848886413388602629066805410659863680948221898966238 : Int) * ((28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (12258570448296220020156397120951265589547158368671571358984495645271716598085 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-6381573656367740974472315766248192864532608116550060587660164636551957641673 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int) =
        (29466273245007724237561535848886413388602629066805410659863680948221898966238 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-16558534706431902508636605060943891288654406033000172898286411877962257709928 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (44648599647213915497370463328261413339747416338771684073573383575116587694472 : Int) =
        (29466273245007724237561535848886413388602629066805410659863680948221898966238 : Int) * ((28324062100449705322624668797990766441943757807898995800682840219674339513338 : Int) - (21393289750074163033520183963327281622799057116362233550947986343578876885527 : Int)) - (12258570448296220020156397120951265589547158368671571358984495645271716598085 : Int) + (-3894738691650313690890003204562692739142646369549852080107490405936069161997 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, doubleX, doubleY, doubleSlope, addX, addY, addSlope] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_three : ∃ output : curve.Equation addX addY,
    (3 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [show (3 : Nat) = 2 + 1 by rfl, add_nsmul, two_nsmul, one_nsmul] using first_add


set_option pp.all true in
#check @baseX
#print axioms baseX

set_option pp.all true in
#check @baseY
#print axioms baseY

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
#check @base_valid
#print axioms base_valid

set_option pp.all true in
#check @base
#print axioms base

set_option pp.all true in
#check @first_double
#print axioms first_double

set_option pp.all true in
#check @first_add
#print axioms first_add

set_option pp.all true in
#check @prefix_three
#print axioms prefix_three
end ShielddSecurity.ConcretePointOperationPilot01
