import ShielddSecurity.ConcretePointTraceStep023
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep024
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 33398432023260150952169772432154959594783542313806192053911600062056019166216
def inputY : F := 36209090643843098286923363715419460461412935510456569776365276736634679399790
def doubleX : F := 7061528283507970242785850827379922959083518798110002142765668792837494593290
def doubleY : F := 4967506470253130231669739979057678864497312948711050361988895724973111008397
def doubleSlope : F := 16750398890667343810175182961499887516576037993458947154855168250512366834341
def addX : F := 28442401694150067458265733757665598455697307560125449373022757812391278344207
def addY : F := 21729355077556603154525861846401546431809362299478912316963800624137387276328
def addSlope : F := 37812117880075089798169282443941176605171132837621557852244928580222774069295
def outX : F := 28442401694150067458265733757665598455697307560125449373022757812391278344207
def outY : F := 21729355077556603154525861846401546431809362299478912316963800624137387276328

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((15194958 : Nat) • base) + ((15194958 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep023.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36209090643843098286923363715419460461412935510456569776365276736634679399790 : Int)) * (29607311836499081394617716609666240611253991833556927293077156468950616693081 : Int) =
        (1 : Int) + (40890090398142913720814211845740999395156446416576568469392904896678787637883 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16750398890667343810175182961499887516576037993458947154855168250512366834341 : Int) * ((2 : Int) * (36209090643843098286923363715419460461412935510456569776365276736634679399790 : Int)) =
        (3 : Int) * (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) + (-40964 : Int) * (-40964 : Int) + (-40684595312019562369473535435594983751152980721416156032250643439119155882116 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int) =
        (16750398890667343810175182961499887516576037993458947154855168250512366834341 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) - (33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) + (-5350837800635498925804847531635765715036259363771469827577747777014425943879 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (4967506470253130231669739979057678864497312948711050361988895724973111008397 : Int) =
        (16750398890667343810175182961499887516576037993458947154855168250512366834341 : Int) * ((33398432023260150952169772432154959594783542313806192053911600062056019166216 : Int) - (7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int)) - (36209090643843098286923363715419460461412935510456569776365276736634679399790 : Int) + (-8413202634886619497435703137541062672345966176121722116569309044291346033083 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((15194958 : Nat) • base) + ((15194958 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (18036271559538453953669707926790281724099679420236910339325711810865246413076 : Int) =
        (1 : Int) + (-11219788465288085112360557154417966909198211912111202046974422716391512140213 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (37812117880075089798169282443941176605171132837621557852244928580222774069295 : Int) * ((7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (4967506470253130231669739979057678864497312948711050361988895724973111008397 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-23521710828013071162419602168946595014891445917723128274075226613291252845322 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int) =
        (37812117880075089798169282443941176605171132837621557852244928580222774069295 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-27266756849229102198924843017134715814409857587993794410451899779386798015101 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21729355077556603154525861846401546431809362299478912316963800624137387276328 : Int) =
        (37812117880075089798169282443941176605171132837621557852244928580222774069295 : Int) * ((7061528283507970242785850827379922959083518798110002142765668792837494593290 : Int) - (28442401694150067458265733757665598455697307560125449373022757812391278344207 : Int)) - (4967506470253130231669739979057678864497312948711050361988895724973111008397 : Int) + (15417995848873833687909654018339580565930979723416530037126202989816698424480 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (30389917 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (30389917 : Nat) = 15194958 + 15194958 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep024
