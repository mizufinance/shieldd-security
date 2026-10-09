import ShielddSecurity.ConcretePointTraceStep187
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep188
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 18695813035194046396366673229820625953850712034663954715333015194480505519419
def inputY : F := 47154185914286160450092003886160297445134984455528562844169721522307633965972
def doubleX : F := 49644790343161489818653784216010388326284852721738683126581900806851282571930
def doubleY : F := 29967760799341343751031199536864949511664896780642297946007166218355447212557
def doubleSlope : F := 50652503537169472656138390523034476703159514594401726132207312971483566630629
def addX : F := 48778507766338317226635242497941196816398462928900331709761482483695027604905
def addY : F := 13179665958852426558520282086353226648631586009618787361528084385530678664564
def addSlope : F := 26385391060976706889131684403398721154762113897130786178039308589090543970577
def outX : F := 48778507766338317226635242497941196816398462928900331709761482483695027604905
def outY : F := 13179665958852426558520282086353226648631586009618787361528084385530678664564

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((355319311131565912440550298393058795571649507227997835394 : Nat) • base) + ((355319311131565912440550298393058795571649507227997835394 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep187.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (47154185914286160450092003886160297445134984455528562844169721522307633965972 : Int)) * (30053518108826372112491764281276493035287300664612892686474528251463855613077 : Int) =
        (1 : Int) + (54052656718284824465089106687720765196517047153109254327876401467868262947399 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (50652503537169472656138390523034476703159514594401726132207312971483566630629 : Int) * ((2 : Int) * (47154185914286160450092003886160297445134984455528562844169721522307633965972 : Int)) =
        (3 : Int) * (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) + (-40964 : Int) * (-40964 : Int) + (71103130252687461312602930135610570153757550298513634638079911520680452929437 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int) =
        (50652503537169472656138390523034476703159514594401726132207312971483566630629 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) - (18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) + (-48929785304699865075363507720405065414025475267964986339391565670214976175057 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29967760799341343751031199536864949511664896780642297946007166218355447212557 : Int) =
        (50652503537169472656138390523034476703159514594401726132207312971483566630629 : Int) * ((18695813035194046396366673229820625953850712034663954715333015194480505519419 : Int) - (49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int)) - (47154185914286160450092003886160297445134984455528562844169721522307633965972 : Int) + (29896386344806078318512347214060835162202846494492390136445180924192160451996 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((355319311131565912440550298393058795571649507227997835394 : Nat) • base) + ((355319311131565912440550298393058795571649507227997835394 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (13643700836139042254176925408733036373356447144004761134650724633258746712604 : Int) =
        (1 : Int) + (2592761786826744431565064594127382661818700471499079046563274959054121877699 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (26385391060976706889131684403398721154762113897130786178039308589090543970577 : Int) * ((49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29967760799341343751031199536864949511664896780642297946007166218355447212557 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (5014111236752948931600328797653828383975463875192718845912171633078353437716 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) =
        (26385391060976706889131684403398721154762113897130786178039308589090543970577 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-13276957028285054926985277134183890934713997046515778759896650520629606345683 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (13179665958852426558520282086353226648631586009618787361528084385530678664564 : Int) =
        (26385391060976706889131684403398721154762113897130786178039308589090543970577 : Int) * ((49644790343161489818653784216010388326284852721738683126581900806851282571930 : Int) - (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int)) - (29967760799341343751031199536864949511664896780642297946007166218355447212557 : Int) + (-435907753660087510164678858279559171316629424284851136187255464695829505408 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (710638622263131824881100596786117591143299014455995670789 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (710638622263131824881100596786117591143299014455995670789 : Nat) = 355319311131565912440550298393058795571649507227997835394 + 355319311131565912440550298393058795571649507227997835394 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep188
