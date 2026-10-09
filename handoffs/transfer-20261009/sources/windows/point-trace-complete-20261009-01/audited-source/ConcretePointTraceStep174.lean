import ShielddSecurity.ConcretePointTraceStep173
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep174
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 8382594515793085882721201356307248973461400156430952611421509330385906310
def inputY : F := 7153271406608474228879463644272109681016934945510705844143638590377569135739
def doubleX : F := 7297327363126440184922607716418021756610312426286230966214985252248030418469
def doubleY : F := 14242845392920676566693420597489916148817088957451360961979646970934300628623
def doubleSlope : F := 33177580452585525670616968694369268477642655463577383695772513229141845046829
def outX : F := 7297327363126440184922607716418021756610312426286230966214985252248030418469
def outY : F := 14242845392920676566693420597489916148817088957451360961979646970934300628623

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((21686969673557489772982806298404467503152435743896352 : Nat) • base) + ((21686969673557489772982806298404467503152435743896352 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep173.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7153271406608474228879463644272109681016934945510705844143638590377569135739 : Int)) * (48331972877600539983164387484657669155658089312230821464445860517853201938944 : Int) =
        (1 : Int) + (13186838913458993820110523919950657849333526196747567279364740180912246668287 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (33177580452585525670616968694369268477642655463577383695772513229141845046829 : Int) * ((2 : Int) * (7153271406608474228879463644272109681016934945510705844143638590377569135739 : Int)) =
        (3 : Int) * (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) + (-40964 : Int) * (-40964 : Int) + (9052128200300412425634224011727324680213116310578813975097235135521773581602 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) =
        (33177580452585525670616968694369268477642655463577383695772513229141845046829 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) - (8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) + (-20992342380316457465170000321141115634757789970579421830581291852429258447040 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (14242845392920676566693420597489916148817088957451360961979646970934300628623 : Int) =
        (33177580452585525670616968694369268477642655463577383695772513229141845046829 : Int) * ((8382594515793085882721201356307248973461400156430952611421509330385906310 : Int) - (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int)) - (7153271406608474228879463644272109681016934945510705844143638590377569135739 : Int) + (4611910274547070215791282181280330498379607669985753258660274269545919821821 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (43373939347114979545965612596808935006304871487792704 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (43373939347114979545965612596808935006304871487792704 : Nat) = 21686969673557489772982806298404467503152435743896352 + 21686969673557489772982806298404467503152435743896352 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep174
