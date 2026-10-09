import ShielddSecurity.ConcretePointTraceStep125
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep126
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25906469863109647471420343926081533993061111892883902574877023483720036516288
def inputY : F := 18473219498009913267560376067107583509183964695431859210229355161621735750192
def doubleX : F := 2259301718970131788569729110226164862188881646159182009880325467411715814243
def doubleY : F := 34242932138417076378741068273486889817211954456052694176935475373037639664703
def doubleSlope : F := 3516974855078297265422462193770795622163620440664922119106551447167696670227
def addX : F := 45711149844443227643209881894737829911885535237635519440527627021383646636483
def addY : F := 286637060483921093632836507847867219039319371102541499388036744422424422876
def addSlope : F := 4634636811495382850823857685740338190269971567331652854712243011406564161111
def outX : F := 45711149844443227643209881894737829911885535237635519440527627021383646636483
def outY : F := 286637060483921093632836507847867219039319371102541499388036744422424422876

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((77047593810979328214411077263450762242 : Nat) • base) + ((77047593810979328214411077263450762242 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep125.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18473219498009913267560376067107583509183964695431859210229355161621735750192 : Int)) * (19641145204346263103535212214482900388636800861531036612507309826112358574285 : Int) =
        (1 : Int) + (13839196364716729548628156027442986605727525427972947354274233595983431086303 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (3516974855078297265422462193770795622163620440664922119106551447167696670227 : Int) * ((2 : Int) * (18473219498009913267560376067107583509183964695431859210229355161621735750192 : Int)) =
        (3 : Int) * (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) + (-40964 : Int) * (-40964 : Int) + (-35919984916441445654313689923821522940036561460704934307103369590219783942384 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int) =
        (3516974855078297265422462193770795622163620440664922119106551447167696670227 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) - (25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) + (-235890258147545888608229210216774706762288592670187143332727326629211365006 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34242932138417076378741068273486889817211954456052694176935475373037639664703 : Int) =
        (3516974855078297265422462193770795622163620440664922119106551447167696670227 : Int) * ((25906469863109647471420343926081533993061111892883902574877023483720036516288 : Int) - (2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int)) - (18473219498009913267560376067107583509183964695431859210229355161621735750192 : Int) + (-1586060983610674618118069114220642263969089162521238485681788154010010347640 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((77047593810979328214411077263450762242 : Nat) • base) + ((77047593810979328214411077263450762242 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (10117763574872495692841569606191620604151934081794853530449696499231361544588 : Int) =
        (1 : Int) + (-7220551123131693178635054382171256048328330208115152516456012644188945380417 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (4634636811495382850823857685740338190269971567331652854712243011406564161111 : Int) * ((2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34242932138417076378741068273486889817211954456052694176935475373037639664703 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-3307512750906733667976427750284719098538806779633192318169282034009477392869 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int) =
        (4634636811495382850823857685740338190269971567331652854712243011406564161111 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-409640504763757786969764182234822016470708896184585311412247410239112465760 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (286637060483921093632836507847867219039319371102541499388036744422424422876 : Int) =
        (4634636811495382850823857685740338190269971567331652854712243011406564161111 : Int) * ((2259301718970131788569729110226164862188881646159182009880325467411715814243 : Int) - (45711149844443227643209881894737829911885535237635519440527627021383646636483 : Int)) - (34242932138417076378741068273486889817211954456052694176935475373037639664703 : Int) + (3840567820738001330428989522537902095172220184763453203869210624805918386363 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (154095187621958656428822154526901524485 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (154095187621958656428822154526901524485 : Nat) = 77047593810979328214411077263450762242 + 77047593810979328214411077263450762242 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep126
