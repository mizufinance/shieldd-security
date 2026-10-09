import ShielddSecurity.ConcretePointTraceStep069
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep070
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41167131855506120034763848086695538957685888449975927237808442306593912360816
def inputY : F := 39344158252348397193155435181087501524005516557562691279107444282911777716185
def doubleX : F := 41586386184076995580728358804587496439741112253455148160366218538217645461961
def doubleY : F := 29039853558911600256095774395393104051336848234891512047921556044202902739775
def doubleSlope : F := 4500740505238763056812739834111317622973916223617445750113010092902542424047
def addX : F := 38529391522479304756200082598569073750811623681082017512231479574297404564283
def addY : F := 8099763043621779494306834975162922283230112941265954589158892124384291713435
def addSlope : F := 40457243947086955558311388951074013296737868103335469755224078910518069984920
def outX : F := 38529391522479304756200082598569073750811623681082017512231479574297404564283
def outY : F := 8099763043621779494306834975162922283230112941265954589158892124384291713435

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1069250158011449517081 : Nat) • base) + ((1069250158011449517081 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep069.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (39344158252348397193155435181087501524005516557562691279107444282911777716185 : Int)) * (16266131074425301239735257107269716403760800202880779739133990250837142875623 : Int) =
        (1 : Int) + (24409900016285587545572254510042540430180838380344350093562928959103920673693 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (4500740505238763056812739834111317622973916223617445750113010092902542424047 : Int) * ((2 : Int) * (39344158252348397193155435181087501524005516557562691279107444282911777716185 : Int)) =
        (3 : Int) * (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) + (-40964 : Int) * (-40964 : Int) + (-90206228587711568959282847618213920518990555495082388462358140540466310674146 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int) =
        (4500740505238763056812739834111317622973916223617445750113010092902542424047 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) - (41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) + (-386313092474252330670481105839665262796399024241297433816338843093449072768 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29039853558911600256095774395393104051336848234891512047921556044202902739775 : Int) =
        (4500740505238763056812739834111317622973916223617445750113010092902542424047 : Int) * ((41167131855506120034763848086695538957685888449975927237808442306593912360816 : Int) - (41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int)) - (39344158252348397193155435181087501524005516557562691279107444282911777716185 : Int) + (35985952981494786187630348020519162393523290121939396710196159189638800175 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1069250158011449517081 : Nat) • base) + ((1069250158011449517081 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12839202450357002949943596422173179435083164739391924851781442119847202539151 : Int) =
        (1 : Int) + (466737005326301853946244013316592156509575413636227344549798369654700629929 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (40457243947086955558311388951074013296737868103335469755224078910518069984920 : Int) * ((41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29039853558911600256095774395393104051336848234891512047921556044202902739775 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1470721639964012394970160830440085912764603881367959101208065143139044974587 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int) =
        (40457243947086955558311388951074013296737868103335469755224078910518069984920 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-31215052334447187204008371954943182895586168885976099758805018657788849233457 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (8099763043621779494306834975162922283230112941265954589158892124384291713435 : Int) =
        (40457243947086955558311388951074013296737868103335469755224078910518069984920 : Int) * ((41586386184076995580728358804587496439741112253455148160366218538217645461961 : Int) - (38529391522479304756200082598569073750811623681082017512231479574297404564283 : Int)) - (29039853558911600256095774395393104051336848234891512047921556044202902739775 : Int) + (-2358644312813315691563597625346766361922981876181848679691050537934144191350 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2138500316022899034163 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2138500316022899034163 : Nat) = 1069250158011449517081 + 1069250158011449517081 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep070
