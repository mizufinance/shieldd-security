import ShielddSecurity.ConcretePointTraceStep077
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep078
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 9530522212558258515445842833019539179108131416257255178908986828912756595823
def inputY : F := 18244361418899087078327179046944438114446479352870520458680288467011164498252
def doubleX : F := 39208270227387732364591386790862044130913910172402094907746622011100779294202
def doubleY : F := 26032005763637724134856836500018549524751750586241939882607429639330329777365
def doubleSlope : F := 18253486730396192579627280490781903400371673468825927331483817547512552414293
def addX : F := 34230780638816084219016197648746680054417524028721541971713619223918003312354
def addY : F := 12393090792878025435157954128918680146178636786741959071352274271779375869943
def addSlope : F := 43637089229010220345407207745567408063462076834433136817714621954709397003209
def outX : F := 34230780638816084219016197648746680054417524028721541971713619223918003312354
def outY : F := 12393090792878025435157954128918680146178636786741959071352274271779375869943

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((273728040450931076372892 : Nat) • base) + ((273728040450931076372892 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep077.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (18244361418899087078327179046944438114446479352870520458680288467011164498252 : Int)) * (24235171735175602090115684658297565373754221262188508956861840009526687932411 : Int) =
        (1 : Int) + (16864607702604911142693379598901902415761096469114852793709164854531456885511 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (18253486730396192579627280490781903400371673468825927331483817547512552414293 : Int) * ((2 : Int) * (18244361418899087078327179046944438114446479352870520458680288467011164498252 : Int)) =
        (3 : Int) * (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) + (-40964 : Int) * (-40964 : Int) + (7505431269760575169475747730720102213050277052511464101778599837778563787509 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int) =
        (18253486730396192579627280490781903400371673468825927331483817547512552414293 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) - (9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) + (-6354233179172794099517124705359531539403341902744647718688253387210100247913 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (26032005763637724134856836500018549524751750586241939882607429639330329777365 : Int) =
        (18253486730396192579627280490781903400371673468825927331483817547512552414293 : Int) * ((9530522212558258515445842833019539179108131416257255178908986828912756595823 : Int) - (39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int)) - (18244361418899087078327179046944438114446479352870520458680288467011164498252 : Int) + (10331140231139053475763306404120028161434137199135578483237431042228447053128 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((273728040450931076372892 : Nat) • base) + ((273728040450931076372892 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (34259977256832320225521215789030011464528745075860139758650861137794825385045 : Int) =
        (1 : Int) + (-308351780296329776208198661494543810586263560161478088487181685770353297742 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (43637089229010220345407207745567408063462076834433136817714621954709397003209 : Int) * ((39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (26032005763637724134856836500018549524751750586241939882607429639330329777365 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-392749068390922838799795317007110022379677980013728595857850604911978430796 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int) =
        (43637089229010220345407207745567408063462076834433136817714621954709397003209 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-36314747298885284817167186344272025209007471167102189431624679988241701230570 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (12393090792878025435157954128918680146178636786741959071352274271779375869943 : Int) =
        (43637089229010220345407207745567408063462076834433136817714621954709397003209 : Int) * ((39208270227387732364591386790862044130913910172402094907746622011100779294202 : Int) - (34230780638816084219016197648746680054417524028721541971713619223918003312354 : Int)) - (26032005763637724134856836500018549524751750586241939882607429639330329777365 : Int) + (-4142262460339447674052181596578794679876455220839173075365603648024318715148 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (547456080901862152745785 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (547456080901862152745785 : Nat) = 273728040450931076372892 + 273728040450931076372892 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep078
