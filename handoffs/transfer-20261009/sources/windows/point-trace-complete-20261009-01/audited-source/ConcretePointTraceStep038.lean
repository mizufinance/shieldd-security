import ShielddSecurity.ConcretePointTraceStep037
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep038
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 40834565630342192016228737739210967477174351999593257180322308603735950747992
def inputY : F := 45652122208100259904850644556775773780974873241917771571196409134802034168290
def doubleX : F := 9048213127048646492967869567094151547602138105212672100034550757801221495275
def doubleY : F := 11657330178250222833957713417516740990573008475139053349836537492852209464217
def doubleSlope : F := 42578164854450553215720898958139343328158508288605006569048533332410807378629
def addX : F := 15764005122552086306320359007029587902914078351527556558239811269606240069132
def addY : F := 34699216161072689576544176653058496837137716526195330229824724896790667213095
def addSlope : F := 45907541199027197908850948408674032285105541762409681776152685715691783998665
def outX : F := 15764005122552086306320359007029587902914078351527556558239811269606240069132
def outY : F := 34699216161072689576544176653058496837137716526195330229824724896790667213095

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((248954202516 : Nat) • base) + ((248954202516 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep037.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (45652122208100259904850644556775773780974873241917771571196409134802034168290 : Int)) * (19843514034993472269035904710229520383392664046466424212644205360190514845374 : Int) =
        (1 : Int) + (34552623551648180811402168585645641396940997269831067991066848431870921958263 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (42578164854450553215720898958139343328158508288605006569048533332410807378629 : Int) * ((2 : Int) * (45652122208100259904850644556775773780974873241917771571196409134802034168290 : Int)) =
        (3 : Int) * (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) + (-40964 : Int) * (-40964 : Int) + (-21260598326410148220894684143436267475087861448986760592810809592810371794812 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int) =
        (42578164854450553215720898958139343328158508288605006569048533332410807378629 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) - (40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) + (-34573660043205437597962552473067956673429912193778932987680069217491150847750 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (11657330178250222833957713417516740990573008475139053349836537492852209464217 : Int) =
        (42578164854450553215720898958139343328158508288605006569048533332410807378629 : Int) * ((40834565630342192016228737739210967477174351999593257180322308603735950747992 : Int) - (9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int)) - (45652122208100259904850644556775773780974873241917771571196409134802034168290 : Int) + (-25810660210910698182946354341211790914616952739532306706562756766981351576422 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((248954202516 : Nat) • base) + ((248954202516 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (14425079647434941914439940403123990636732120885266429757412329942625487699849 : Int) =
        (1 : Int) + (-8426845438439477630620634164516736932192420118192159015436359311303587897961 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (45907541199027197908850948408674032285105541762409681776152685715691783998665 : Int) * ((9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (11657330178250222833957713417516740990573008475139053349836537492852209464217 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-26818275087429771212644709590374929611295702502670113567400363250947985595607 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int) =
        (45907541199027197908850948408674032285105541762409681776152685715691783998665 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-40191993208880539847883160567989224808455940784825053849850122961065696628431 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (34699216161072689576544176653058496837137716526195330229824724896790667213095 : Int) =
        (45907541199027197908850948408674032285105541762409681776152685715691783998665 : Int) * ((9048213127048646492967869567094151547602138105212672100034550757801221495275 : Int) - (15764005122552086306320359007029587902914078351527556558239811269606240069132 : Int)) - (11657330178250222833957713417516740990573008475139053349836537492852209464217 : Int) + (5879667244763008448206797594975779957263084665100391983539225588750165655209 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (497908405033 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (497908405033 : Nat) = 248954202516 + 248954202516 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep038
