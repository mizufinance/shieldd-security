import ShielddSecurity.ConcretePointTraceStep065
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep066
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 44294910295909989985030859079862652884137397789573722871361170914723888399577
def inputY : F := 3280129060165482175056426065849754617191188015626397827911265233395713389453
def doubleX : F := 27246355347733043096319264690764141429491267103145364720752691528920689263976
def doubleY : F := 51981931539222603042016098138432607010701448965461853544882737087921453910032
def doubleSlope : F := 14763415892935131581974053908995890633767195947744368717542859832967606694395
def addX : F := 30239546712992809695573208682375305651971921206300777841516633041370378850264
def addY : F := 28108137010333261335632345513343544414478736331499131446870039524044997268852
def addSlope : F := 30365246410918487124797154462171581594686834142251870739974649143638086576436
def outX : F := 30239546712992809695573208682375305651971921206300777841516633041370378850264
def outY : F := 28108137010333261335632345513343544414478736331499131446870039524044997268852

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((66828134875715594817 : Nat) • base) + ((66828134875715594817 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep065.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3280129060165482175056426065849754617191188015626397827911265233395713389453 : Int)) * (2068954725028614755529662418918118057336895468446188113561882139435954869178 : Int) =
        (1 : Int) + (258847153597325714739177393514036048502187642298818109157020768568888121059 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (14763415892935131581974053908995890633767195947744368717542859832967606694395 : Int) * ((2 : Int) * (3280129060165482175056426065849754617191188015626397827911265233395713389453 : Int)) =
        (3 : Int) * (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) + (-40964 : Int) * (-40964 : Int) + (-110406575575168805961840180352676232583545116599950693738718759129699744883157 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int) =
        (14763415892935131581974053908995890633767195947744368717542859832967606694395 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) - (44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) + (-4156666558912737682474555540099738416372933880252058309665651427432987327751 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (51981931539222603042016098138432607010701448965461853544882737087921453910032 : Int) =
        (14763415892935131581974053908995890633767195947744368717542859832967606694395 : Int) * ((44294910295909989985030859079862652884137397789573722871361170914723888399577 : Int) - (27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int)) - (3280129060165482175056426065849754617191188015626397827911265233395713389453 : Int) + (-4800051610331260108882570975441525522464803556866780518330412077534023457070 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((66828134875715594817 : Nat) • base) + ((66828134875715594817 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34066637827204059541051579498439098286556731360604082824541605049768147448119 : Int) =
        (1 : Int) + (-8078050974179921580895065747540355015370357103541639417256858036018942883518 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (30365246410918487124797154462171581594686834142251870739974649143638086576436 : Int) * ((27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (51981931539222603042016098138432607010701448965461853544882737087921453910032 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-7200358591156726023043135384205995245035732191475027394166611558945063499426 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int) =
        (30365246410918487124797154462171581594686834142251870739974649143638086576436 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-17584300567432630679254075260735039703059766765973774000144795033619969996357 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (28108137010333261335632345513343544414478736331499131446870039524044997268852 : Int) =
        (30365246410918487124797154462171581594686834142251870739974649143638086576436 : Int) * ((27246355347733043096319264690764141429491267103145364720752691528920689263976 : Int) - (30239546712992809695573208682375305651971921206300777841516633041370378850264 : Int)) - (51981931539222603042016098138432607010701448965461853544882737087921453910032 : Int) + (1733336061572230708321060950118399663968821921927696875947414611372392180804 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (133656269751431189635 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (133656269751431189635 : Nat) = 66828134875715594817 + 66828134875715594817 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep066
