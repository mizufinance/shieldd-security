import ShielddSecurity.ConcretePointTraceStep048
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep049
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 1279391236065245694412774766013593245181292891422121742832157962491225052482
def inputY : F := 30603730848310519894531228960730461671625641126484444369896559406189214429621
def doubleX : F := 51397671773341204811543285788838463790699887969835410149525971415448702800434
def doubleY : F := 43887994078981160786853413648996314351472468652497309757903751228285008925419
def doubleSlope : F := 51368624252709676692636837532900866019258800025873184105365203674909111965549
def addX : F := 20913556524983791022230689091847888476849531022843889115802912294324893617294
def addY : F := 49968519463943887879853582934281343552674315037296074161330315232503280538420
def addSlope : F := 42588609429909167648059564494816703759996247325769072960857649243844815185282
def outX : F := 20913556524983791022230689091847888476849531022843889115802912294324893617294
def outY : F := 49968519463943887879853582934281343552674315037296074161330315232503280538420

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((509858206754421 : Nat) • base) + ((509858206754421 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep048.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (30603730848310519894531228960730461671625641126484444369896559406189214429621 : Int)) * (5006774836261684873277504739044493763104275196518523437078391176469632731770 : Int) =
        (1 : Int) + (5844318951301944350378440231631786393153080557998943339219172391726461289603 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (51368624252709676692636837532900866019258800025873184105365203674909111965549 : Int) * ((2 : Int) * (30603730848310519894531228960730461671625641126484444369896559406189214429621 : Int)) =
        (3 : Int) * (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) + (-40964 : Int) * (-40964 : Int) + (59868030524266531854682105416396417520261368376671140446304753050498039447334 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int) =
        (51368624252709676692636837532900866019258800025873184105365203674909111965549 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) - (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) + (-50323095567742137807780823407396152928592648105241826221943506169493237467067 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (43887994078981160786853413648996314351472468652497309757903751228285008925419 : Int) =
        (51368624252709676692636837532900866019258800025873184105365203674909111965549 : Int) * ((1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) - (51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int)) - (30603730848310519894531228960730461671625641126484444369896559406189214429621 : Int) + (49098200659621687598005672738026603770512736199871058492045197191717136352976 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((509858206754421 : Nat) • base) + ((509858206754421 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (20174793818858784808006063297018867817766000348765153358122897880433071407265 : Int) =
        (1 : Int) + (4508313160951183902826371400973157040089948725709866073856839255626929086078 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (42588609429909167648059564494816703759996247325769072960857649243844815185282 : Int) * ((51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (43887994078981160786853413648996314351472468652497309757903751228285008925419 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (9516964095067520340727530260508901764873339853919312230802328249274830756093 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int) =
        (42588609429909167648059564494816703759996247325769072960857649243844815185282 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-34590624207484357494106994461719296049583772834705571361756664772127068999737 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (49968519463943887879853582934281343552674315037296074161330315232503280538420 : Int) =
        (42588609429909167648059564494816703759996247325769072960857649243844815185282 : Int) * ((51397671773341204811543285788838463790699887969835410149525971415448702800434 : Int) - (20913556524983791022230689091847888476849531022843889115802912294324893617294 : Int)) - (43887994078981160786853413648996314351472468652497309757903751228285008925419 : Int) + (-24759309800639901532044201304160038602843271142052773010621521543669523458857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1019716413508843 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1019716413508843 : Nat) = 509858206754421 + 509858206754421 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep049
