import ShielddSecurity.ConcretePointTraceStep155
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep156
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 38076020991662553201322953943009372428476307892225054745374619609001492473576
def inputY : F := 27959162627871934623588781124288107643747688433377718058143673159688839425130
def doubleX : F := 35398969559109969022919939900817362118928086950472060943195111204695522747363
def doubleY : F := 46373265022301119758910421681695759453284313616250788346001359047681775888566
def doubleSlope : F := 48212318166245915790262446256995869668278990528876511080690260094730359855817
def addX : F := 12097625452536914439360317234161396025970551999657340922646029728917320644396
def addY : F := 10904485311615268752083358961102852905051872603172247544652655847981267497571
def addSlope : F := 39092167150541746734631733498126765507450072100752095331433867807208512311160
def outX : F := 12097625452536914439360317234161396025970551999657340922646029728917320644396
def outY : F := 10904485311615268752083358961102852905051872603172247544652655847981267497571

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((82729223913412055103236413186662549984559767699 : Nat) • base) + ((82729223913412055103236413186662549984559767699 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep155.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (27959162627871934623588781124288107643747688433377718058143673159688839425130 : Int)) * (51528207946894135634963865018723189025090989960686392518103192732615921263518 : Int) =
        (1 : Int) + (54950376668583906750140703423501811072751833627701055581136769441798883757783 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (48212318166245915790262446256995869668278990528876511080690260094730359855817 : Int) * ((2 : Int) * (27959162627871934623588781124288107643747688433377718058143673159688839425130 : Int)) =
        (3 : Int) * (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) + (-40964 : Int) * (-40964 : Int) + (-31531809655068949602579125001173311883694024681260423102008497816620383068636 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int) =
        (48212318166245915790262446256995869668278990528876511080690260094730359855817 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) - (38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) + (-44328956371952688628743165825241538719477705284046837255862818900649287991334 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (46373265022301119758910421681695759453284313616250788346001359047681775888566 : Int) =
        (48212318166245915790262446256995869668278990528876511080690260094730359855817 : Int) * ((38076020991662553201322953943009372428476307892225054745374619609001492473576 : Int) - (35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int)) - (27959162627871934623588781124288107643747688433377718058143673159688839425130 : Int) + (-2461422737440159432561851157061497209322685842661254755916593795950515096525 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((82729223913412055103236413186662549984559767699 : Nat) • base) + ((82729223913412055103236413186662549984559767699 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (25435553955389401899483096543600715203045656284407958618112157465231076885870 : Int) =
        (1 : Int) + (-2076741518666368817551519310491259117303243066527648194702639852828708425377 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (39092167150541746734631733498126765507450072100752095331433867807208512311160 : Int) * ((35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (46373265022301119758910421681695759453284313616250788346001359047681775888566 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-3191765617472384365121051052783987463611794418084449990126125229082105801740 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int) =
        (39092167150541746734631733498126765507450072100752095331433867807208512311160 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-29144121794897028141464465012442825986928515008082703225435723323339745969702 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (10904485311615268752083358961102852905051872603172247544652655847981267497571 : Int) =
        (39092167150541746734631733498126765507450072100752095331433867807208512311160 : Int) * ((35398969559109969022919939900817362118928086950472060943195111204695522747363 : Int) - (12097625452536914439360317234161396025970551999657340922646029728917320644396 : Int)) - (46373265022301119758910421681695759453284313616250788346001359047681775888566 : Int) + (-17371695153446107195799643612387038934472317662241385692676889162233176937391 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (165458447826824110206472826373325099969119535399 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (165458447826824110206472826373325099969119535399 : Nat) = 82729223913412055103236413186662549984559767699 + 82729223913412055103236413186662549984559767699 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep156
