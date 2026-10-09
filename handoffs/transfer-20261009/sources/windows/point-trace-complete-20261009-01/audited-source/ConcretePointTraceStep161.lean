import ShielddSecurity.ConcretePointTraceStep160
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep161
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 14921983627863233452171159185278874711105732371475696218170192373884026736564
def inputY : F := 19102744592094582575807867208215381237214898910546985844095458571759001678282
def doubleX : F := 39954678219646971810405399660911258919990664196973491988774962142988766832309
def doubleY : F := 38472036842726139148130814547387551787539611455241190984592348898955646281534
def doubleSlope : F := 976164539399373486427058349305330978712055351990510371757825850334164707599
def addX : F := 15404267638426985390272097218400946617754616138581192216781492137569353797187
def addY : F := 4072985716889950744564801902672042965456180286556136476577763122841076849901
def addSlope : F := 41155347180342113160720383928434542116577814273157532128289310296121272780094
def outX : F := 15404267638426985390272097218400946617754616138581192216781492137569353797187
def outY : F := 4072985716889950744564801902672042965456180286556136476577763122841076849901

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2647335165229185763303565221973201599505912566393 : Nat) • base) + ((2647335165229185763303565221973201599505912566393 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep160.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (19102744592094582575807867208215381237214898910546985844095458571759001678282 : Int)) * (23072715699664737723666576056346119230792295088666455401565138642801873443819 : Int) =
        (1 : Int) + (16811093305286694556767625068300537308537027957119812133670970691164200436955 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (976164539399373486427058349305330978712055351990510371757825850334164707599 : Int) * ((2 : Int) * (19102744592094582575807867208215381237214898910546985844095458571759001678282 : Int)) =
        (3 : Int) * (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) + (-40964 : Int) * (-40964 : Int) + (-12028061709892602536266045532682617518115514342529902697012070675242419109588 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int) =
        (976164539399373486427058349305330978712055351990510371757825850334164707599 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) - (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) + (-18172619505220221207552266670170591919709835753377853684270640905552988364 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (38472036842726139148130814547387551787539611455241190984592348898955646281534 : Int) =
        (976164539399373486427058349305330978712055351990510371757825850334164707599 : Int) * ((14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) - (39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int)) - (19102744592094582575807867208215381237214898910546985844095458571759001678282 : Int) + (466017372733875680949774856469448532943291183606288601562186742326578354967 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2647335165229185763303565221973201599505912566393 : Nat) • base) + ((2647335165229185763303565221973201599505912566393 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (22489311739749964909838576528780399749992415652669953262107313046945944632099 : Int) =
        (1 : Int) + (117716521071010480607609343681482265252687587315576426301873809781701757221 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (41155347180342113160720383928434542116577814273157532128289310296121272780094 : Int) * ((39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (38472036842726139148130814547387551787539611455241190984592348898955646281534 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (215420745178987717627720526380740136012880637769333215576415185789310383912 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int) =
        (41155347180342113160720383928434542116577814273157532128289310296121272780094 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-32301598779035108761715277894853358851512296220332463805092170774442836090625 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (4072985716889950744564801902672042965456180286556136476577763122841076849901 : Int) =
        (41155347180342113160720383928434542116577814273157532128289310296121272780094 : Int) * ((39954678219646971810405399660911258919990664196973491988774962142988766832309 : Int) - (15404267638426985390272097218400946617754616138581192216781492137569353797187 : Int)) - (38472036842726139148130814547387551787539611455241190984592348898955646281534 : Int) + (-19268881610454051093799652298270733091923764957756970222393335108745125405041 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5294670330458371526607130443946403199011825132787 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (5294670330458371526607130443946403199011825132787 : Nat) = 2647335165229185763303565221973201599505912566393 + 2647335165229185763303565221973201599505912566393 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep161
