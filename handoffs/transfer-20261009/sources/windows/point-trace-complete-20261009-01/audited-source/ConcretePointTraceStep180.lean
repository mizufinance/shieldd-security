import ShielddSecurity.ConcretePointTraceStep179
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep180
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 24931452984497419997275362289213400635533747478699840205571758617794644805676
def inputY : F := 49201152357153201905421578983094378007312177511861083693393688811743793787408
def doubleX : F := 5011839948685678185874977536910005645511711514884381783720373842674471583408
def doubleY : F := 22573858811406476005523874261912021768507834139626058598509801195721409209336
def doubleSlope : F := 13532343734762262530739824759368876278244424683254571368982523098214315818546
def addX : F := 48014335250910506609650122023600251861286839797659429155557026589364830311449
def addY : F := 24877379213436662361660366021259612104203269489146406808559010533597043643226
def addSlope : F := 2049581759458775572509426228648110972700994334282857079692647047873739707221
def outX : F := 48014335250910506609650122023600251861286839797659429155557026589364830311449
def outY : F := 24877379213436662361660366021259612104203269489146406808559010533597043643226

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1387966059107679345470899603097885920201755887609366544 : Nat) • base) + ((1387966059107679345470899603097885920201755887609366544 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep179.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (49201152357153201905421578983094378007312177511861083693393688811743793787408 : Int)) * (33124319117401737583907937139547414996304309956327883991133025774556554405026 : Int) =
        (1 : Int) + (62161818265802340728141128537343008205353267002378668642555635521209055829055 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13532343734762262530739824759368876278244424683254571368982523098214315818546 : Int) * ((2 : Int) * (49201152357153201905421578983094378007312177511861083693393688811743793787408 : Int)) =
        (3 : Int) * (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) + (-40964 : Int) * (-40964 : Int) + (-10167051284779507520766446098474900144106597950352950366780456480439664608704 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int) =
        (13532343734762262530739824759368876278244424683254571368982523098214315818546 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) - (24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) + (-3492348060257559319805876704907645593837997685805771729490196337989247447748 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (22573858811406476005523874261912021768507834139626058598509801195721409209336 : Int) =
        (13532343734762262530739824759368876278244424683254571368982523098214315818546 : Int) * ((24931452984497419997275362289213400635533747478699840205571758617794644805676 : Int) - (5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int)) - (49201152357153201905421578983094378007312177511861083693393688811743793787408 : Int) + (-5140737133952241781487867221346351311134192734881524026494732282414155729968 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1387966059107679345470899603097885920201755887609366544 : Nat) • base) + ((1387966059107679345470899603097885920201755887609366544 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (27962133208642618043296735993703903457514085700098205869256363445097318276348 : Int) =
        (1 : Int) + (-18487373744293693484290047007319648163671062278735781198656057495702896661877 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (2049581759458775572509426228648110972700994334282857079692647047873739707221 : Int) * ((5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (22573858811406476005523874261912021768507834139626058598509801195721409209336 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-1355096327017348590971837452600023389464206992014454753161314730944786258605 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int) =
        (2049581759458775572509426228648110972700994334282857079692647047873739707221 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-80112811594662598227257332230246919694010596718251385935837291365456986213 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (24877379213436662361660366021259612104203269489146406808559010533597043643226 : Int) =
        (2049581759458775572509426228648110972700994334282857079692647047873739707221 : Int) * ((5011839948685678185874977536910005645511711514884381783720373842674471583408 : Int) - (48014335250910506609650122023600251861286839797659429155557026589364830311449 : Int)) - (22573858811406476005523874261912021768507834139626058598509801195721409209336 : Int) + (1680855515203853692378853528153166513697036502116945591332908933667320487471 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2775932118215358690941799206195771840403511775218733089 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2775932118215358690941799206195771840403511775218733089 : Nat) = 1387966059107679345470899603097885920201755887609366544 + 1387966059107679345470899603097885920201755887609366544 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep180
