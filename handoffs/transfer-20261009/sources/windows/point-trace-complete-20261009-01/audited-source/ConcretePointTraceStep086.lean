import ShielddSecurity.ConcretePointTraceStep085
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep086
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 10378987859999056781139591117833698048571862064924587164826879234824060711809
def inputY : F := 41718627792011559039542361908761065287226788854555695085040170064263241996038
def doubleX : F := 42591097252687136101871060178937715056399434788651233410864144025707176688131
def doubleY : F := 46275955570477297471008499519235276853342775312990446581249123430270068215578
def doubleSlope : F := 36517629994496054773920244894916123533816966475917427071706727820586433071386
def outX : F := 42591097252687136101871060178937715056399434788651233410864144025707176688131
def outY : F := 46275955570477297471008499519235276853342775312990446581249123430270068215578

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((70074378355438355551460588 : Nat) • base) + ((70074378355438355551460588 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep085.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (41718627792011559039542361908761065287226788854555695085040170064263241996038 : Int)) * (51137337405072114959565827247725788565355201541151215598072241215296733994425 : Int) =
        (1 : Int) + (81370990313468327584984232112118447041837387075468102638761842603176998052523 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (36517629994496054773920244894916123533816966475917427071706727820586433071386 : Int) * ((2 : Int) * (41718627792011559039542361908761065287226788854555695085040170064263241996038 : Int)) =
        (3 : Int) * (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) + (-40964 : Int) * (-40964 : Int) + (51944601879584776813752274438413078324475074105567285495745363123278437080117 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int) =
        (36517629994496054773920244894916123533816966475917427071706727820586433071386 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) - (10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) + (-25431773494027673234642107359516129095618202177711730453488636584213912466855 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (46275955570477297471008499519235276853342775312990446581249123430270068215578 : Int) =
        (36517629994496054773920244894916123533816966475917427071706727820586433071386 : Int) * ((10378987859999056781139591117833698048571862064924587164826879234824060711809 : Int) - (42591097252687136101871060178937715056399434788651233410864144025707176688131 : Int)) - (41718627792011559039542361908761065287226788854555695085040170064263241996038 : Int) + (22433303310295772726767612591092788042291575973357177972882669900878882840916 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (140148756710876711102921176 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (140148756710876711102921176 : Nat) = 70074378355438355551460588 + 70074378355438355551460588 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep086
