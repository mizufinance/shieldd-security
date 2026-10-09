import ShielddSecurity.ConcretePointTraceStep230
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep231
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 34877913436063020738398167695095977309175058417401779269709656337699354728823
def inputY : F := 42166255922519058322045855362693485245378823701561069765451221737270197566327
def doubleX : F := 4764004295310067396169238057790232358204452713129015329294328728678833025697
def doubleY : F := 33335885486926770853204249205216746383058774791740217094404687771440555254720
def doubleSlope : F := 6554379677401426562159726993874600726299200038842247819021426852601926852261
def addX : F := 26135607416669294830319148679467983493474699676934555071851097571110023699135
def addY : F := 42164768287188290499734729018657824321642417346628537911637086305717290187165
def addSlope : F := 318863558503877633377346189136163751249202718383532166762776913580590028420
def outX : F := 26135607416669294830319148679467983493474699676934555071851097571110023699135
def outY : F := 42164768287188290499734729018657824321642417346628537911637086305717290187165

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) • base) + ((3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep230.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42166255922519058322045855362693485245378823701561069765451221737270197566327 : Int)) * (37384323961084939705477530689041125891422904652157962515056966142597509876127 : Int) =
        (1 : Int) + (60125132511614472971096529340819674604771228860550673605777580985318605863889 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (6554379677401426562159726993874600726299200038842247819021426852601926852261 : Int) * ((2 : Int) * (42166255922519058322045855362693485245378823701561069765451221737270197566327 : Int)) =
        (3 : Int) * (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) + (-40964 : Int) * (-40964 : Int) + (-59056118064910908283616432373437109335999967614116405816156493171256900074797 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int) =
        (6554379677401426562159726993874600726299200038842247819021426852601926852261 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) - (34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) + (-819284369948144813115894190061441818342479260521388701847835763387132588242 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33335885486926770853204249205216746383058774791740217094404687771440555254720 : Int) =
        (6554379677401426562159726993874600726299200038842247819021426852601926852261 : Int) * ((34877913436063020738398167695095977309175058417401779269709656337699354728823 : Int) - (4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int)) - (42166255922519058322045855362693485245378823701561069765451221737270197566327 : Int) + (-3764178502219291115201176358057199536709669802003181571223515428823201234103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) • base) + ((3125421713300120263066753179322836747029266961036833420450858670421687 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (36663680516552914093175676907579502982229143549624821347041163389387680467976 : Int) =
        (1 : Int) + (-24413756032407268382915237378020423777369472142529952908429286070030141455249 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (318863558503877633377346189136163751249202718383532166762776913580590028420 : Int) * ((4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (33335885486926770853204249205216746383058774791740217094404687771440555254720 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-212326122616748049767846598527555153432199362721449443877323477764104089438 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) =
        (318863558503877633377346189136163751249202718383532166762776913580590028420 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1939015389791500870526638586010121075408342620518330638955550053231542181 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42164768287188290499734729018657824321642417346628537911637086305717290187165 : Int) =
        (318863558503877633377346189136163751249202718383532166762776913580590028420 : Int) * ((4764004295310067396169238057790232358204452713129015329294328728678833025697 : Int) - (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int)) - (33335885486926770853204249205216746383058774791740217094404687771440555254720 : Int) + (129961126794386187169324599216790066154034798949383004285992109865568100565 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (6250843426600240526133506358645673494058533922073666840901717340843375 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (6250843426600240526133506358645673494058533922073666840901717340843375 : Nat) = 3125421713300120263066753179322836747029266961036833420450858670421687 + 3125421713300120263066753179322836747029266961036833420450858670421687 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep231
