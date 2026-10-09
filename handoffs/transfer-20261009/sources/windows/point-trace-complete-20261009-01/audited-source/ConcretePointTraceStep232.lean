import ShielddSecurity.ConcretePointTraceStep231
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep232
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26135607416669294830319148679467983493474699676934555071851097571110023699135
def inputY : F := 42164768287188290499734729018657824321642417346628537911637086305717290187165
def doubleX : F := 17161984629568680313537620642466397382453008231007114871551079266105585589916
def doubleY : F := 3293007701218363759454646524264533698937855837419325108187892371439148683618
def doubleSlope : F := 24925670052836737043529536228010915992969394800059370786086074935486868171749
def outX : F := 17161984629568680313537620642466397382453008231007114871551079266105585589916
def outY : F := 3293007701218363759454646524264533698937855837419325108187892371439148683618

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((6250843426600240526133506358645673494058533922073666840901717340843375 : Nat) • base) + ((6250843426600240526133506358645673494058533922073666840901717340843375 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep231.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42164768287188290499734729018657824321642417346628537911637086305717290187165 : Int)) * (31862043899393746910096032503034859374898036443571397649446335114227221157563 : Int) =
        (1 : Int) + (51241852784463437018393473014730872746529521116694797884709892219634347452253 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24925670052836737043529536228010915992969394800059370786086074935486868171749 : Int) * ((2 : Int) * (42164768287188290499734729018657824321642417346628537911637086305717290187165 : Int)) =
        (3 : Int) * (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) + (-40964 : Int) * (-40964 : Int) + (1006186681743212437386065917398263081887764787013830669026931864707617844543 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) =
        (24925670052836737043529536228010915992969394800059370786086074935486868171749 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) - (26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) + (-11848548832414657444141421643144860906842532709874991189479515260576549627591 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3293007701218363759454646524264533698937855837419325108187892371439148683618 : Int) =
        (24925670052836737043529536228010915992969394800059370786086074935486868171749 : Int) * ((26135607416669294830319148679467983493474699676934555071851097571110023699135 : Int) - (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int)) - (42164768287188290499734729018657824321642417346628537911637086305717290187165 : Int) + (-4265658960069961990923017930300834009065033438995332850932243619604409590096 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) = 6250843426600240526133506358645673494058533922073666840901717340843375 + 6250843426600240526133506358645673494058533922073666840901717340843375 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep232
