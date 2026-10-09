import ShielddSecurity.ConcretePointTraceStep104
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep105
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39326180973746726893678134031361786199996369071432450876244551372792576949573
def inputY : F := 23491918829854771203082160344717548861507358379830210409762103516625509777034
def doubleX : F := 19741304051159236018216544009456474464575910693819951819392426212187980317133
def doubleY : F := 9809932962426492212709650482200057397485679506307358160253080180549078553848
def doubleSlope : F := 2506322198513752337069356442531760736363097475113462713936937128474416731979
def addX : F := 13796702754189404292833322356193779546928824053480762761012684000557665146781
def addY : F := 16070313979432645508107480497018209570929959795736087263749848496893827904414
def addSlope : F := 32271098446735804816800771669426135752240611087625155129883765205910897895302
def outX : F := 13796702754189404292833322356193779546928824053480762761012684000557665146781
def outY : F := 16070313979432645508107480497018209570929959795736087263749848496893827904414

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((36739155679216064555364168769574 : Nat) • base) + ((36739155679216064555364168769574 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep104.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (23491918829854771203082160344717548861507358379830210409762103516625509777034 : Int)) * (39945183490600271905727704085951591544010059447741364164091817131413387682270 : Int) =
        (1 : Int) + (35791869786507407827962782714023348110178269327221647249650239264299267853143 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (2506322198513752337069356442531760736363097475113462713936937128474416731979 : Int) * ((2 : Int) * (23491918829854771203082160344717548861507358379830210409762103516625509777034 : Int)) =
        (3 : Int) * (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) + (-40964 : Int) * (-40964 : Int) + (-86236548537417607767901955532886921550306101990249769827368797801344793942191 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int) =
        (2506322198513752337069356442531760736363097475113462713936937128474416731979 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) - (39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) + (-119796817384724651156439142620262659198257603491742174814802918271047504810 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (9809932962426492212709650482200057397485679506307358160253080180549078553848 : Int) =
        (2506322198513752337069356442531760736363097475113462713936937128474416731979 : Int) * ((39326180973746726893678134031361786199996369071432450876244551372792576949573 : Int) - (19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int)) - (23491918829854771203082160344717548861507358379830210409762103516625509777034 : Int) + (-936115047613918336050929099311097140370249478281168232012384483919582781606 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((36739155679216064555364168769574 : Nat) • base) + ((36739155679216064555364168769574 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12471091016286582327742160963589211423737646072595810313577218930409023220516 : Int) =
        (1 : Int) + (-4742171806466980271430618369784968516669720859194291151237596575467785813977 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (32271098446735804816800771669426135752240611087625155129883765205910897895302 : Int) * ((19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (9809932962426492212709650482200057397485679506307358160253080180549078553848 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-12271187261641759413759638791589700225924882735546136544545064283624828106354 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int) =
        (32271098446735804816800771669426135752240611087625155129883765205910897895302 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-19860902320801358065450695279976076847796780058313895346031685124749658937775 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (16070313979432645508107480497018209570929959795736087263749848496893827904414 : Int) =
        (32271098446735804816800771669426135752240611087625155129883765205910897895302 : Int) * ((19741304051159236018216544009456474464575910693819951819392426212187980317133 : Int) - (13796702754189404292833322356193779546928824053480762761012684000557665146781 : Int)) - (9809932962426492212709650482200057397485679506307358160253080180549078553848 : Int) + (-3658541276185443476627265241570587561012948846841184471165185930979657604234 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (73478311358432129110728337539149 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (73478311358432129110728337539149 : Nat) = 36739155679216064555364168769574 + 36739155679216064555364168769574 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep105
