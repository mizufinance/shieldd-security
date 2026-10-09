import ShielddSecurity.ConcretePointTraceStep237
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep238
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 17712398429480140543225274045226700555426202639752176633171691637089529533040
def inputY : F := 28221329087306292075191320043939257391181579682548264477267534273737245139042
def doubleX : F := 31345499497497006541885073005994203384030141036915838122675996528556479201625
def doubleY : F := 26951858898313312045051701165394280006149860025391140538001366118251031542261
def doubleSlope : F := 44984585092954289985128518086230818140173201586531067793812244844761074945696
def addX : F := 47052145210969971302795790239996070489609335243951289405893096745473092469831
def addY : F := 9947332390387807912193310390222834115829054029959453814488073969674945730262
def addSlope : F := 9452132846230898142869862017627221709304679556846052357400950440899731220238
def outX : F := 47052145210969971302795790239996070489609335243951289405893096745473092469831
def outY : F := 9947332390387807912193310390222834115829054029959453814488073969674945730262

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) • base) + ((400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep237.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (28221329087306292075191320043939257391181579682548264477267534273737245139042 : Int)) * (30207946801904707083575307254188409194945322871140299977377772359514444929314 : Int) =
        (1 : Int) + (32516226911486569751955976371727923090502804626537009833725831740421860474375 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (44984585092954289985128518086230818140173201586531067793812244844761074945696 : Int) * ((2 : Int) * (28221329087306292075191320043939257391181579682548264477267534273737245139042 : Int)) =
        (3 : Int) * (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) + (-40964 : Int) * (-40964 : Int) + (30472694120540057099390279579578008605119963696847592936398981047424552175216 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int) =
        (44984585092954289985128518086230818140173201586531067793812244844761074945696 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) - (17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) + (-38592144962332563285306350233370491013546530758929722489536947198493112581583 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (26951858898313312045051701165394280006149860025391140538001366118251031542261 : Int) =
        (44984585092954289985128518086230818140173201586531067793812244844761074945696 : Int) * ((17712398429480140543225274045226700555426202639752176633171691637089529533040 : Int) - (31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int)) - (28221329087306292075191320043939257391181579682548264477267534273737245139042 : Int) + (11695797829764644939725940979993793715709110882199851973440510181966978460151 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) • base) + ((400053979302415393672544406953323103619746171012714677817709909813976028 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (9926891148030421966078729019344863034573819980209252460464525616436716851321 : Int) =
        (1 : Int) + (-1577884949947182123721050520509350964449818569427814144180325470482345161963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (9452132846230898142869862017627221709304679556846052357400950440899731220238 : Int) * ((31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (26951858898313312045051701165394280006149860025391140538001366118251031542261 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-1502421849959369595257042871029714804497115279695810728862898809019306300663 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) =
        (9452132846230898142869862017627221709304679556846052357400950440899731220238 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-1703849035501141705316413679999510636428141704252213571740921401320739280921 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (9947332390387807912193310390222834115829054029959453814488073969674945730262 : Int) =
        (9452132846230898142869862017627221709304679556846052357400950440899731220238 : Int) * ((31345499497497006541885073005994203384030141036915838122675996528556479201625 : Int) - (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int)) - (26951858898313312045051701165394280006149860025391140538001366118251031542261 : Int) + (2831292533148270622210430679561501603244665438226672518095870240931260414927 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (800107958604830787345088813906646207239492342025429355635419819627952057 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (800107958604830787345088813906646207239492342025429355635419819627952057 : Nat) = 400053979302415393672544406953323103619746171012714677817709909813976028 + 400053979302415393672544406953323103619746171012714677817709909813976028 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep238
