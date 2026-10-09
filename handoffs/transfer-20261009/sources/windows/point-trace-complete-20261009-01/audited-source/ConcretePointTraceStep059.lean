import ShielddSecurity.ConcretePointTraceStep058
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep059
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9748009729789797770934086729667614535774896700998054132724512323837044997140
def inputY : F := 33007109801971083240139360097564809980050493546141416887888037303055264752138
def doubleX : F := 45013135387325283946051425128695506619948140321649102139061187138456518098975
def doubleY : F := 22275196967264842628218785375794157248920269382692193095146284434009168782113
def doubleSlope : F := 15175621678380757562534039744717283332482692907930519640532469785595677327229
def addX : F := 20725644920209728775432975754999927469548718699481902153929074922766755937601
def addY : F := 8408705082890901898326845248907802312667179307170059442596528453140901587345
def addSlope : F := 38942900376148623108145923308393957858910111490212346644711565644988690094802
def outX : F := 20725644920209728775432975754999927469548718699481902153929074922766755937601
def outY : F := 8408705082890901898326845248907802312667179307170059442596528453140901587345

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((522094803716528084 : Nat) • base) + ((522094803716528084 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep058.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33007109801971083240139360097564809980050493546141416887888037303055264752138 : Int)) * (21494891024854978703111597465509159081775585643456559710001921226513225785577 : Int) =
        (1 : Int) + (27061023616722102657484988024895003195735468481784789528214715032684797195827 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15175621678380757562534039744717283332482692907930519640532469785595677327229 : Int) * ((2 : Int) * (33007109801971083240139360097564809980050493546141416887888037303055264752138 : Int)) =
        (3 : Int) * (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) + (-40964 : Int) * (-40964 : Int) + (13668804775985474104605866122634847321043594260239116004425907631254330787396 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int) =
        (15175621678380757562534039744717283332482692907930519640532469785595677327229 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) - (9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) + (-4392021541667455726224849531049783658864710081686150374263990168367854291658 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (22275196967264842628218785375794157248920269382692193095146284434009168782113 : Int) =
        (15175621678380757562534039744717283332482692907930519640532469785595677327229 : Int) * ((9748009729789797770934086729667614535774896700998054132724512323837044997140 : Int) - (45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int)) - (33007109801971083240139360097564809980050493546141416887888037303055264752138 : Int) + (10206184289514513057850835974521259531333956303323080603977990617341167743882 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((522094803716528084 : Nat) • base) + ((522094803716528084 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (38127381696507314277544930024393258149173520511270047396317843746796013984021 : Int) =
        (1 : Int) + (3877696823781592560626477682624065535865128129765136242136378837433884129787 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (38942900376148623108145923308393957858910111490212346644711565644988690094802 : Int) * ((45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (22275196967264842628218785375794157248920269382692193095146284434009168782113 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (3960638113035382291008661756318425965892954444270627015412039744862468336609 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int) =
        (38942900376148623108145923308393957858910111490212346644711565644988690094802 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-28921982986679250982188836349595916707153586797583569268140652017493051043801 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (8408705082890901898326845248907802312667179307170059442596528453140901587345 : Int) =
        (38942900376148623108145923308393957858910111490212346644711565644988690094802 : Int) * ((45013135387325283946051425128695506619948140321649102139061187138456518098975 : Int) - (20725644920209728775432975754999927469548718699481902153929074922766755937601 : Int)) - (22275196967264842628218785375794157248920269382692193095146284434009168782113 : Int) + (-18037752178039512598181914890317428537653695381947980356414720051396923578730 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1044189607433056169 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1044189607433056169 : Nat) = 522094803716528084 + 522094803716528084 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep059
