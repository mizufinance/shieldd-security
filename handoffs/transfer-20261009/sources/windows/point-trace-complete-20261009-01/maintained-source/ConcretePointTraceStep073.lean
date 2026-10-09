import ShielddSecurity.ConcretePointTraceStep072
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep073
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 34815630181111615896387691440911280968407745606240415350511026765795559601951
def inputY : F := 33025881838446418669896895652124036313110170179930101567712181109501807640510
def doubleX : F := 35655317476976168274599407678781211627244895954048893093632698332935437126228
def doubleY : F := 34122380825147958856998185075419357973357316918559187806348208179683671248561
def doubleSlope : F := 8797234722430360396034523397909566557545757810250943292960868277680642969928
def addX : F := 34253846517722219294123708534716221629448590821177048022499316921823396196802
def addY : F := 28965364953740762307463463105675419620314025364945790956642152856696220347478
def addSlope : F := 25179222059803879199715778117881950966319561810376657146693600938850650955706
def outX : F := 34253846517722219294123708534716221629448590821177048022499316921823396196802
def outY : F := 28965364953740762307463463105675419620314025364945790956642152856696220347478

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((8554001264091596136652 : Nat) • base) + ((8554001264091596136652 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep072.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33025881838446418669896895652124036313110170179930101567712181109501807640510 : Int)) * (35957014458925115468494340971359418179496427742828980134513279855753477466193 : Int) =
        (1 : Int) + (45293879688960962300720015857507685705468650334303198195942462691690141955643 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (8797234722430360396034523397909566557545757810250943292960868277680642969928 : Int) * ((2 : Int) * (33025881838446418669896895652124036313110170179930101567712181109501807640510 : Int)) =
        (3 : Int) * (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) + (-40964 : Int) * (-40964 : Int) + (-58267577982125502121238200937711790639283468487578791455432193146232419481731 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int) =
        (8797234722430360396034523397909566557545757810250943292960868277680642969928 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) - (34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) + (-1475923468485298007272289965746324127710520840285696869621626189243861101494 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34122380825147958856998185075419357973357316918559187806348208179683671248561 : Int) =
        (8797234722430360396034523397909566557545757810250943292960868277680642969928 : Int) * ((34815630181111615896387691440911280968407745606240415350511026765795559601951 : Int) - (35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int)) - (33025881838446418669896895652124036313110170179930101567712181109501807640510 : Int) + (140875425660243463463442469164397592268622863687567129282289029403180104279 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((8554001264091596136652 : Nat) • base) + ((8554001264091596136652 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (47795528075780268979652392978516413707503169099518501127840306992819285918260 : Int) =
        (1 : Int) + (-3668708343656066275403048190735020643086217958245975817084775757783475049677 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (25179222059803879199715778117881950966319561810376657146693600938850650955706 : Int) * ((35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34122380825147958856998185075419357973357316918559187806348208179683671248561 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-1932716841439842926147144039803898682569870946552333148164131835486154245965 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int) =
        (25179222059803879199715778117881950966319561810376657146693600938850650955706 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-12090829444907582925139611717749360039689175564354039871870125085178125512707 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (28965364953740762307463463105675419620314025364945790956642152856696220347478 : Int) =
        (25179222059803879199715778117881950966319561810376657146693600938850650955706 : Int) * ((35655317476976168274599407678781211627244895954048893093632698332935437126228 : Int) - (34253846517722219294123708534716221629448590821177048022499316921823396196802 : Int)) - (34122380825147958856998185075419357973357316918559187806348208179683671248561 : Int) + (-672973386551979350479100470405294623017658974573178579168851933023889853709 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (17108002528183192273305 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (17108002528183192273305 : Nat) = 8554001264091596136652 + 8554001264091596136652 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep073
