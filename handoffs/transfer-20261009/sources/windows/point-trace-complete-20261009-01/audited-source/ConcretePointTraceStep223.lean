import ShielddSecurity.ConcretePointTraceStep222
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep223
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41947726929964311439622386140736546154831328010705607939974728641541653178062
def inputY : F := 24011830238690429127330354905040574902778815943680823329702414212912642775825
def doubleX : F := 33892459687188856886129976589176225310341168435038950320522371719596701614721
def doubleY : F := 20899666170021268889933873811362736005300322497074225796445795115322387168993
def doubleSlope : F := 1280121032705279217597835734871573860153527498603405091283341389046536827734
def addX : F := 15181243147482961138848927792205229419202939875801041645726413033511828683555
def addY : F := 22621897723724176282109242261266287259090309777626480277263534638136596413319
def addSlope : F := 30377356586539688107348957567581529929030651896846803375028414453121863960768
def outX : F := 15181243147482961138848927792205229419202939875801041645726413033511828683555
def outY : F := 22621897723724176282109242261266287259090309777626480277263534638136596413319

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((12208678567578594777604504606729831043083074066550130548636166681334 : Nat) • base) + ((12208678567578594777604504606729831043083074066550130548636166681334 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep222.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24011830238690429127330354905040574902778815943680823329702414212912642775825 : Int)) * (16738009656845683955404724569218288921985151982478756135719293029875525984437 : Int) =
        (1 : Int) + (15329590478710738250386363068089305456527440801105137667553460085775592523273 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (1280121032705279217597835734871573860153527498603405091283341389046536827734 : Int) * ((2 : Int) * (24011830238690429127330354905040574902778815943680823329702414212912642775825 : Int)) =
        (3 : Int) * (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) + (-40964 : Int) * (-40964 : Int) + (-99499803684079750581620967326755960463090698644577613111978108215074265925392 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int) =
        (1280121032705279217597835734871573860153527498603405091283341389046536827734 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) - (41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) + (-31251692718037806225454388195381640169178949454644282957017291378141515983 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (20899666170021268889933873811362736005300322497074225796445795115322387168993 : Int) =
        (1280121032705279217597835734871573860153527498603405091283341389046536827734 : Int) * ((41947726929964311439622386140736546154831328010705607939974728641541653178062 : Int) - (33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int)) - (24011830238690429127330354905040574902778815943680823329702414212912642775825 : Int) + (-196653855534964972795397739767173035493337499469149147482239919563777404652 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((12208678567578594777604504606729831043083074066550130548636166681334 : Nat) • base) + ((12208678567578594777604504606729831043083074066550130548636166681334 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (17825775124329872473240467704363473844812562801782175128746079977061499709599 : Int) =
        (1 : Int) + (-1967568215598121558311966968775102464783787849426226887457397411171329853103 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (30377356586539688107348957567581529929030651896846803375028414453121863960768 : Int) * ((33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (20899666170021268889933873811362736005300322497074225796445795115322387168993 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-3352983019065919313441697138361924299452738459638367938746544836135144304951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int) =
        (30377356586539688107348957567581529929030651896846803375028414453121863960768 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-17598329199309782092551421839680603502797986005155555017320478567252530850641 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (22621897723724176282109242261266287259090309777626480277263534638136596413319 : Int) =
        (30377356586539688107348957567581529929030651896846803375028414453121863960768 : Int) * ((33892459687188856886129976589176225310341168435038950320522371719596701614721 : Int) - (15181243147482961138848927792205229419202939875801041645726413033511828683555 : Int)) - (20899666170021268889933873811362736005300322497074225796445795115322387168993 : Int) + (-10839855253607624318451377696447893071928214527203966386779723366425306774552 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (24417357135157189555209009213459662086166148133100261097272333362669 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (24417357135157189555209009213459662086166148133100261097272333362669 : Nat) = 12208678567578594777604504606729831043083074066550130548636166681334 + 12208678567578594777604504606729831043083074066550130548636166681334 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep223
