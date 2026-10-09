import ShielddSecurity.ConcretePointTraceStep200
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep201
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 27917619233653858553474252533019435221491774704687086999359922332967845712847
def inputY : F := 17240713838745046324314945059024113113341998238135875130352949585740987791529
def doubleX : F := 22857720916332086666244222424450086091595086563135228849267637596194943257460
def doubleY : F := 24858984447170626990871405147228897411904129405269218214098920307305076444111
def doubleSlope : F := 7305798506534903741789741117633360340507104477770528051931311009330307458978
def addX : F := 12189058057469396823932366284755724066207170687485414246282943715765456356768
def addY : F := 27827872333113970240299072461453037450701473764736709678527325927296938478706
def addSlope : F := 27404797936688178439376204128638533469005267543649607020530057669861600954607
def outX : F := 12189058057469396823932366284755724066207170687485414246282943715765456356768
def outY : F := 27827872333113970240299072461453037450701473764736709678527325927296938478706

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2910775796789787954712988044435937653322952763211758267554322 : Nat) • base) + ((2910775796789787954712988044435937653322952763211758267554322 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep200.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (17240713838745046324314945059024113113341998238135875130352949585740987791529 : Int)) * (4150716382575331905472810887348555491300033774685903943144193976159313574330 : Int) =
        (1 : Int) + (2729479126219240630971292718620093670161542082496510149749107462531188365203 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (7305798506534903741789741117633360340507104477770528051931311009330307458978 : Int) * ((2 : Int) * (17240713838745046324314945059024113113341998238135875130352949585740987791529 : Int)) =
        (3 : Int) * (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) + (-40964 : Int) * (-40964 : Int) + (-39786997379727064238379069276932429801185253071749463529211901229931612287839 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int) =
        (7305798506534903741789741117633360340507104477770528051931311009330307458978 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) - (27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) + (-1017904090278382202025384191970079774762714577284120866240578282119143034746 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (24858984447170626990871405147228897411904129405269218214098920307305076444111 : Int) =
        (7305798506534903741789741117633360340507104477770528051931311009330307458978 : Int) * ((27917619233653858553474252533019435221491774704687086999359922332967845712847 : Int) - (22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int)) - (17240713838745046324314945059024113113341998238135875130352949585740987791529 : Int) + (-704986756613601441642908693350997139834162037966129400959716911828663706142 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2910775796789787954712988044435937653322952763211758267554322 : Nat) • base) + ((2910775796789787954712988044435937653322952763211758267554322 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (19330410735743797843979148209699614967029485336848819230051202099578050351018 : Int) =
        (1 : Int) + (-6201587185800037156534074263899749807952467332672155726493762283123430140055 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (27404797936688178439376204128638533469005267543649607020530057669861600954607 : Int) * ((22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (24858984447170626990871405147228897411904129405269218214098920307305076444111 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-8792014098249072938634364053954786949787489049264885186908552468276526727702 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int) =
        (27404797936688178439376204128638533469005267543649607020530057669861600954607 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-14322693145531183645996799040690009893333402745459264595080718888971546760962 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (27827872333113970240299072461453037450701473764736709678527325927296938478706 : Int) =
        (27404797936688178439376204128638533469005267543649607020530057669861600954607 : Int) * ((22857720916332086666244222424450086091595086563135228849267637596194943257460 : Int) - (12189058057469396823932366284755724066207170687485414246282943715765456356768 : Int)) - (24858984447170626990871405147228897411904129405269218214098920307305076444111 : Int) + (-5575811387247975523890397728710923991381912098637554860318256139968210679979 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5821551593579575909425976088871875306645905526423516535108645 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (5821551593579575909425976088871875306645905526423516535108645 : Nat) = 2910775796789787954712988044435937653322952763211758267554322 + 2910775796789787954712988044435937653322952763211758267554322 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep201
