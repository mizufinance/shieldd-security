import ShielddSecurity.ConcretePointTraceStep114
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep115
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 28242056687444847643758468803987694961131337139329849831101088473582876704369
def inputY : F := 16348322006186725381924241635900085310008306328641021847733362873200594801659
def doubleX : F := 40028285630424548968492228770968595464436122034237203343730159109251921569636
def doubleY : F := 29827548732836245123786990672917542330917604214125912082337880273838461802540
def doubleSlope : F := 45474116401711620949003434513482521007795851453217814043523486665195607307523
def addX : F := 9561349938457233516426805880378293824940136867818816209920931006976062285907
def addY : F := 17164809337310362779433859245001725753978060608604374250305735702192664356769
def addSlope : F := 48229456363130132517173843202872034690722491501123190812537498818016983681163
def outX : F := 9561349938457233516426805880378293824940136867818816209920931006976062285907
def outY : F := 17164809337310362779433859245001725753978060608604374250305735702192664356769

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((37620895415517250104692908820044317 : Nat) • base) + ((37620895415517250104692908820044317 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep114.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16348322006186725381924241635900085310008306328641021847733362873200594801659 : Int)) * (742642418103149413981493530371787574971925813174534818768705247833265782120 : Int) =
        (1 : Int) + (463078277841453897186785502944522157138436864207740328769691957670090037743 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (45474116401711620949003434513482521007795851453217814043523486665195607307523 : Int) * ((2 : Int) * (16348322006186725381924241635900085310008306328641021847733362873200594801659 : Int)) =
        (3 : Int) * (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) + (-40964 : Int) * (-40964 : Int) + (-17278061995164683432873120692725234770497601194542373905696066150751233670337 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int) =
        (45474116401711620949003434513482521007795851453217814043523486665195607307523 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) - (28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) + (-39436650110444949405824446594155200488407557553656672857149452724530026125771 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29827548732836245123786990672917542330917604214125912082337880273838461802540 : Int) =
        (45474116401711620949003434513482521007795851453217814043523486665195607307523 : Int) * ((28242056687444847643758468803987694961131337139329849831101088473582876704369 : Int) - (40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int)) - (16348322006186725381924241635900085310008306328641021847733362873200594801659 : Int) + (10221405575862816009087120687352053344286731774700008481471775139895293703680 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((37620895415517250104692908820044317 : Nat) • base) + ((37620895415517250104692908820044317 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (40082524912051049338180429195845787113116577315929959809251780207349632763283 : Int) =
        (1 : Int) + (266071502929890330886928208682042115444139162804501560957588890534717801346 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (48229456363130132517173843202872034690722491501123190812537498818016983681163 : Int) * ((40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29827548732836245123786990672917542330917604214125912082337880273838461802540 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (320151586462843670612944911603286527440098409089999094037926183405173679865 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int) =
        (48229456363130132517173843202872034690722491501123190812537498818016983681163 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-44360477503510567828740443382352743082163845323705044576413820906099750667447 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (17164809337310362779433859245001725753978060608604374250305735702192664356769 : Int) =
        (48229456363130132517173843202872034690722491501123190812537498818016983681163 : Int) * ((40028285630424548968492228770968595464436122034237203343730159109251921569636 : Int) - (9561349938457233516426805880378293824940136867818816209920931006976062285907 : Int)) - (29827548732836245123786990672917542330917604214125912082337880273838461802540 : Int) + (-28022870612276251948182518473705030123515897919240000064731310751596300043886 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (75241790831034500209385817640088635 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (75241790831034500209385817640088635 : Nat) = 37620895415517250104692908820044317 + 37620895415517250104692908820044317 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep115
