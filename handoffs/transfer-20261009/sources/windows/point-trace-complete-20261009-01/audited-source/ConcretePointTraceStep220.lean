import ShielddSecurity.ConcretePointTraceStep219
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep220
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11345426754867998811639614315686321865344235522776571584934044162566692450284
def inputY : F := 45289242538100592905525736493705885725582717681764829608109119467416520630401
def doubleX : F := 27995234882581068290475164312569601877335634375878366279535282801734794584220
def doubleY : F := 50204195615384779958480745026962370948327395573487607699829611921660863753245
def doubleSlope : F := 24854620990223508624507116244615126780224349926498124022334669811113082783817
def addX : F := 5426695565711702682421420025351840595683857721779550813188589146006034759360
def addY : F := 27176793175848885822729853230278611057591852422142903882448268509402730353669
def addSlope : F := 29475813048920849412586123826995887260580463706623916166335964507172677271392
def outX : F := 5426695565711702682421420025351840595683857721779550813188589146006034759360
def outY : F := 27176793175848885822729853230278611057591852422142903882448268509402730353669

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1526084820947324347200563075841228880385384258318766318579520835166 : Nat) • base) + ((1526084820947324347200563075841228880385384258318766318579520835166 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep219.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (45289242538100592905525736493705885725582717681764829608109119467416520630401 : Int)) * (5820492834163564364160170170667015473848725597693803510879697253376719666622 : Int) =
        (1 : Int) + (10054403050480821660703918762008409505148039578458728629626897178722082732411 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (24854620990223508624507116244615126780224349926498124022334669811113082783817 : Int) * ((2 : Int) * (45289242538100592905525736493705885725582717681764829608109119467416520630401 : Int)) =
        (3 : Int) * (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) + (-40964 : Int) * (-40964 : Int) + (35569880076534536519642549951380191746657433411057491239124103536256424219538 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int) =
        (24854620990223508624507116244615126780224349926498124022334669811113082783817 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) - (11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) + (-11781098007890212771570369221031952692342183608737730136181570220632564851813 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (50204195615384779958480745026962370948327395573487607699829611921660863753245 : Int) =
        (24854620990223508624507116244615126780224349926498124022334669811113082783817 : Int) * ((11345426754867998811639614315686321865344235522776571584934044162566692450284 : Int) - (27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int)) - (45289242538100592905525736493705885725582717681764829608109119467416520630401 : Int) + (7892014182888201141297723065260593972091264965132422221635946533728764751566 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1526084820947324347200563075841228880385384258318766318579520835166 : Nat) • base) + ((1526084820947324347200563075841228880385384258318766318579520835166 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (25702035546853549510385726258164301037253761058740605591172527228023425134686 : Int) =
        (1 : Int) + (-5727523037008255735815655590815126459870888962088570330337208462196206038963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (29475813048920849412586123826995887260580463706623916166335964507172677271392 : Int) * ((27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (50204195615384779958480745026962370948327395573487607699829611921660863753245 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-6568483572613770113579677046470144421424592897749755884608682371840551392915 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) =
        (29475813048920849412586123826995887260580463706623916166335964507172677271392 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-16569258203343065264850385001557272220247852793659065858313136269499655445913 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (27176793175848885822729853230278611057591852422142903882448268509402730353669 : Int) =
        (29475813048920849412586123826995887260580463706623916166335964507172677271392 : Int) * ((27995234882581068290475164312569601877335634375878366279535282801734794584220 : Int) - (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int)) - (50204195615384779958480745026962370948327395573487607699829611921660863753245 : Int) + (-12686467870890463649271836188924590690991426094768605831867964278918640096862 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3052169641894648694401126151682457760770768516637532637159041670333 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3052169641894648694401126151682457760770768516637532637159041670333 : Nat) = 1526084820947324347200563075841228880385384258318766318579520835166 + 1526084820947324347200563075841228880385384258318766318579520835166 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep220
