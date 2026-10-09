import ShielddSecurity.ConcretePointTraceStep064
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep065
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39614047561310823587481091238856254897733127891130228102422155395408029290677
def inputY : F := 15821335370192190507577400118331906245328277898888636965530052816553626505425
def doubleX : F := 35543747523994633722511192419246299539087892981459078608217047769068210963014
def doubleY : F := 38409139674795556321974606522187445804765424573722630477648152354312263413485
def doubleSlope : F := 12064949435997015020542568463736645953874616367781321924133239817916074744097
def addX : F := 44294910295909989985030859079862652884137397789573722871361170914723888399577
def addY : F := 3280129060165482175056426065849754617191188015626397827911265233395713389453
def addSlope : F := 2404094409901883320773653874205881172205878507063210190080375015998949580920
def outX : F := 44294910295909989985030859079862652884137397789573722871361170914723888399577
def outY : F := 3280129060165482175056426065849754617191188015626397827911265233395713389453

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((33414067437857797408 : Nat) • base) + ((33414067437857797408 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep064.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15821335370192190507577400118331906245328277898888636965530052816553626505425 : Int)) * (21481731129115287427593142229791489576992134757724344094818132914590113045412 : Int) =
        (1 : Int) + (12963249736594575652393915292370633732044460911894523314171316965016202682823 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (12064949435997015020542568463736645953874616367781321924133239817916074744097 : Int) * ((2 : Int) * (15821335370192190507577400118331906245328277898888636965530052816553626505425 : Int)) =
        (3 : Int) * (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) + (-40964 : Int) * (-40964 : Int) + (-82501742473421724605758362599965704853544365063837936095444420249748221930697 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int) =
        (12064949435997015020542568463736645953874616367781321924133239817916074744097 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) - (39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) + (-2776019364738568676497056606990069923771199954073031560577526968595355619993 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (38409139674795556321974606522187445804765424573722630477648152354312263413485 : Int) =
        (12064949435997015020542568463736645953874616367781321924133239817916074744097 : Int) * ((39614047561310823587481091238856254897733127891130228102422155395408029290677 : Int) - (35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int)) - (15821335370192190507577400118331906245328277898888636965530052816553626505425 : Int) + (-936533699028480313078729031410986604027724638901886589427762616122979775377 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((33414067437857797408 : Nat) • base) + ((33414067437857797408 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (27966681767814819987891059533824798262835340480672021444817384661809831192321 : Int) =
        (1 : Int) + (-2206183644336900330133908666636309257355207566250197184829178259614717337550 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (2404094409901883320773653874205881172205878507063210190080375015998949580920 : Int) * ((35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (38409139674795556321974606522187445804765424573722630477648152354312263413485 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-189649734301736778269000768692255373072749619821804599904921391175808025563 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) =
        (2404094409901883320773653874205881172205878507063210190080375015998949580920 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-110223580943742213669884561569300798313655943311579261253677254639834057238 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (3280129060165482175056426065849754617191188015626397827911265233395713389453 : Int) =
        (2404094409901883320773653874205881172205878507063210190080375015998949580920 : Int) * ((35543747523994633722511192419246299539087892981459078608217047769068210963014 : Int) - (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int)) - (38409139674795556321974606522187445804765424573722630477648152354312263413485 : Int) + (401225714834319957319388001845122413723120756115841996215430248092091234146 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (66828134875715594817 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (66828134875715594817 : Nat) = 33414067437857797408 + 33414067437857797408 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep065
