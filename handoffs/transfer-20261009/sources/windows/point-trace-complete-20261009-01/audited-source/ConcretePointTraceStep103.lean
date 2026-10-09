import ShielddSecurity.ConcretePointTraceStep102
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep103
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4135579946183550342138252281696287041372198289593503635539368313089709755681
def inputY : F := 46716454846539337129234035002814852559935032755158051812237089092077353354247
def doubleX : F := 42500031487073143287556780952736584011946860001497056106360906804988099924698
def doubleY : F := 21308950647039504336523137333956378355245652193952544781641716856088492302311
def doubleSlope : F := 22315064846841873284210527502731324300587959730185461960611824043880472539372
def addX : F := 25288452322634376891223605381290424442664373563926490493860152509141197031420
def addY : F := 35007192162067712850367973838231061448427204670773025696442100853824346579598
def addSlope : F := 49031529301813311386491132982338837737656115582346529447353589161372933246352
def outX : F := 25288452322634376891223605381290424442664373563926490493860152509141197031420
def outY : F := 35007192162067712850367973838231061448427204670773025696442100853824346579598

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((9184788919804016138841042192393 : Nat) • base) + ((9184788919804016138841042192393 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep102.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (46716454846539337129234035002814852559935032755158051812237089092077353354247 : Int)) * (20657489637540477458932317117906647832238293953612903628491181196896595766330 : Int) =
        (1 : Int) + (36808565840541118710533070289548719033913375476827454906347061674712525617963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22315064846841873284210527502731324300587959730185461960611824043880472539372 : Int) * ((2 : Int) * (46716454846539337129234035002814852559935032755158051812237089092077353354247 : Int)) =
        (3 : Int) * (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) + (-40964 : Int) * (-40964 : Int) + (38783606974505894868054648549096907126009874353600759102787693886680266523685 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int) =
        (22315064846841873284210527502731324300587959730185461960611824043880472539372 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) - (4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) + (-9496592122390556401392426439748406339366062839874044698705727127039195868284 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21308950647039504336523137333956378355245652193952544781641716856088492302311 : Int) =
        (22315064846841873284210527502731324300587959730185461960611824043880472539372 : Int) * ((4135579946183550342138252281696287041372198289593503635539368313089709755681 : Int) - (42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int)) - (46716454846539337129234035002814852559935032755158051812237089092077353354247 : Int) + (16326708023642967999835928779665434372223183600501681999553919245675426273914 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((9184788919804016138841042192393 : Nat) • base) + ((9184788919804016138841042192393 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (44531309132125284056737400315922281696842593664646881564446199263351606016602 : Int) =
        (1 : Int) + (2394739812534086400656290945727709547660783588618890204675157413828172102133 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (49031529301813311386491132982338837737656115582346529447353589161372933246352 : Int) * ((42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (21308950647039504336523137333956378355245652193952544781641716856088492302311 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (2636746091162582876059491034624971408557970198886906649276085845630403208755 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int) =
        (49031529301813311386491132982338837737656115582346529447353589161372933246352 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-45848207122420585087873814730961197124793571401998368179848692956602825223967 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (35007192162067712850367973838231061448427204670773025696442100853824346579598 : Int) =
        (49031529301813311386491132982338837737656115582346529447353589161372933246352 : Int) * ((42500031487073143287556780952736584011946860001497056106360906804988099924698 : Int) - (25288452322634376891223605381290424442664373563926490493860152509141197031420 : Int)) - (21308950647039504336523137333956378355245652193952544781641716856088492302311 : Int) + (-16094134889770683006398378386222283246678674292140535037227812945459841933419 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (18369577839608032277682084384787 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (18369577839608032277682084384787 : Nat) = 9184788919804016138841042192393 + 9184788919804016138841042192393 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep103
