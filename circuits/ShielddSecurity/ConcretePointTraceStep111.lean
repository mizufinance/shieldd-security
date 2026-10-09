import ShielddSecurity.ConcretePointTraceStep110
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep111
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 5777692232401321805871635376245319506092271805702286665435652113265054685369
def inputY : F := 24063447353574249502388842604895712446190708337747710149904611869615006664861
def doubleX : F := 13425812177720169285809332693494289163358538059689343347851889090887886141569
def doubleY : F := 15372877149410347241712776009024768086114248723778794112730087350688232056783
def doubleSlope : F := 51518776598436949761214025013228911916542832241373242049194987185993632935765
def addX : F := 3937438753608230034618003978372154230051041743589846586894599496688287252225
def addY : F := 35997831797499231780797956312155720429329632056191926696093734804943318124453
def addSlope : F := 16179908491825287205816101467547528728847456491104526710928559986865980931464
def outX : F := 3937438753608230034618003978372154230051041743589846586894599496688287252225
def outY : F := 35997831797499231780797956312155720429329632056191926696093734804943318124453

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2351305963469828131543306801252769 : Nat) • base) + ((2351305963469828131543306801252769 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep110.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24063447353574249502388842604895712446190708337747710149904611869615006664861 : Int)) * (168752164253966235527908512362361303853858661120350363253466369429149346805 : Int) =
        (1 : Int) + (154884754255167569469903577770910291330543242551080923259992811890231294593 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (51518776598436949761214025013228911916542832241373242049194987185993632935765 : Int) * ((2 : Int) * (24063447353574249502388842604895712446190708337747710149904611869615006664861 : Int)) =
        (3 : Int) * (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) + (-40964 : Int) * (-40964 : Int) + (45375299759003279559591534097304649781616520923450081994006774767964361246895 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int) =
        (51518776598436949761214025013228911916542832241373242049194987185993632935765 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) - (5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) + (-50617717990501094249496116503523671432869348937792375221733340788546162387022 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15372877149410347241712776009024768086114248723778794112730087350688232056783 : Int) =
        (51518776598436949761214025013228911916542832241373242049194987185993632935765 : Int) * ((5777692232401321805871635376245319506092271805702286665435652113265054685369 : Int) - (13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int)) - (24063447353574249502388842604895712446190708337747710149904611869615006664861 : Int) + (7514355039273610890321948852248512456743336798081545535509691697266240517588 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2351305963469828131543306801252769 : Nat) • base) + ((2351305963469828131543306801252769 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (50698708048313171894797003249829444555560424986756545190398169299133049747040 : Int) =
        (1 : Int) + (-25384607753910509739473239778521092031039660583238028761446422077397475541697 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (16179908491825287205816101467547528728847456491104526710928559986865980931464 : Int) * ((13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (15372877149410347241712776009024768086114248723778794112730087350688232056783 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-8101205067548383560550264817691068984283995358099280289031283868094013170741 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int) =
        (16179908491825287205816101467547528728847456491104526710928559986865980931464 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-4992563544129117818851573014807718943649735952689142792155393758786903538099 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (35997831797499231780797956312155720429329632056191926696093734804943318124453 : Int) =
        (16179908491825287205816101467547528728847456491104526710928559986865980931464 : Int) * ((13425812177720169285809332693494289163358538059689343347851889090887886141569 : Int) - (3937438753608230034618003978372154230051041743589846586894599496688287252225 : Int)) - (15372877149410347241712776009024768086114248723778794112730087350688232056783 : Int) + (-2927785857023767783708660407090926178702886951760783939878986867559046405260 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4702611926939656263086613602505539 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (4702611926939656263086613602505539 : Nat) = 2351305963469828131543306801252769 + 2351305963469828131543306801252769 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep111
