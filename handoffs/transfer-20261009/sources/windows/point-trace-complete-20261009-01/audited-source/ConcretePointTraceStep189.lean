import ShielddSecurity.ConcretePointTraceStep188
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep189
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48778507766338317226635242497941196816398462928900331709761482483695027604905
def inputY : F := 13179665958852426558520282086353226648631586009618787361528084385530678664564
def doubleX : F := 49553765634450325166472065227529522110491168019613166274559874790959434150783
def doubleY : F := 15638688736840558302971814753388385715529539611841249927134233223736397308681
def doubleSlope : F := 50611189418042916918762101390582312234090563411144695706858843484667499763001
def addX : F := 6969037676750295985428532703249517442761901418630701637489494608086960821417
def addY : F := 21465722024821691164279013471078412042773282418695313593283447497924060391024
def addSlope : F := 36522091572939625200247299801804802158868658927054235327318444915671896612095
def outX : F := 6969037676750295985428532703249517442761901418630701637489494608086960821417
def outY : F := 21465722024821691164279013471078412042773282418695313593283447497924060391024

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((710638622263131824881100596786117591143299014455995670789 : Nat) • base) + ((710638622263131824881100596786117591143299014455995670789 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep188.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (13179665958852426558520282086353226648631586009618787361528084385530678664564 : Int)) * (6557830295980862549847493427239808835180907469162603553949769772563657299115 : Int) =
        (1 : Int) + (3296598461538393019033308809801666873956571873896899768129412118643970799863 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (50611189418042916918762101390582312234090563411144695706858843484667499763001 : Int) * ((2 : Int) * (13179665958852426558520282086353226648631586009618787361528084385530678664564 : Int)) =
        (3 : Int) * (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) + (-40964 : Int) * (-40964 : Int) + (-110686649163917386976496368195689507153786496913629937399282391879626143911051 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int) =
        (50611189418042916918762101390582312234090563411144695706858843484667499763001 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) - (48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) + (-48849999847510982759746293170362044913793349918479926972003760910548868683752 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15638688736840558302971814753388385715529539611841249927134233223736397308681 : Int) =
        (50611189418042916918762101390582312234090563411144695706858843484667499763001 : Int) * ((48778507766338317226635242497941196816398462928900331709761482483695027604905 : Int) - (49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int)) - (13179665958852426558520282086353226648631586009618787361528084385530678664564 : Int) + (748280116996264890426172926173855315124773586513331000263405428948351367971 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((710638622263131824881100596786117591143299014455995670789 : Nat) • base) + ((710638622263131824881100596786117591143299014455995670789 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (6513299682449744025944708644954601506229082897634873403069141559444350401251 : Int) =
        (1 : Int) + (1226439286783440839807356971195690160734976875037376387968209995590821264323 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (36522091572939625200247299801804802158868658927054235327318444915671896612095 : Int) * ((49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (15638688736840558302971814753388385715529539611841249927134233223736397308681 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (6877025490052169200143288420175286157945680096211164040934015434274640762805 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int) =
        (36522091572939625200247299801804802158868658927054235327318444915671896612095 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-25437988179034480174936186135013697859499543396821464577477184816366339659470 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21465722024821691164279013471078412042773282418695313593283447497924060391024 : Int) =
        (36522091572939625200247299801804802158868658927054235327318444915671896612095 : Int) * ((49553765634450325166472065227529522110491168019613166274559874790959434150783 : Int) - (6969037676750295985428532703249517442761901418630701637489494608086960821417 : Int)) - (15638688736840558302971814753388385715529539611841249927134233223736397308681 : Int) + (-29660672752871618248458982353381166680723006797114213994988029320775734531505 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1421277244526263649762201193572235182286598028911991341579 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1421277244526263649762201193572235182286598028911991341579 : Nat) = 710638622263131824881100596786117591143299014455995670789 + 710638622263131824881100596786117591143299014455995670789 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep189
