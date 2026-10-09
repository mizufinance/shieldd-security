import ShielddSecurity.ConcretePointTraceStep192
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep193
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3247695854547107748213455149549234035978018092181694894252872548824707302566
def inputY : F := 13074162549871009910548949283150339436620277388484112828409316766144365683819
def doubleX : F := 28351713828157723238237498368422776453633195243955962703556456885277541961457
def doubleY : F := 1910096758335463814148690304927784567117063602611275147333593907816339921721
def doubleSlope : F := 407405153332789281129834882431923018387634784368827950607958599389691014119
def outX : F := 28351713828157723238237498368422776453633195243955962703556456885277541961457
def outY : F := 1910096758335463814148690304927784567117063602611275147333593907816339921721

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((11370217956210109198097609548577881458292784231295930732634 : Nat) • base) + ((11370217956210109198097609548577881458292784231295930732634 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep192.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (13074162549871009910548949283150339436620277388484112828409316766144365683819 : Int)) * (25713926933000804603227486701852903868574889429936598038954445973100319565105 : Int) =
        (1 : Int) + (12822826333869789468110495365681207584490756059467258168904773110280766545653 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (407405153332789281129834882431923018387634784368827950607958599389691014119 : Int) * ((2 : Int) * (13074162549871009910548949283150339436620277388484112828409316766144365683819 : Int)) =
        (3 : Int) * (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) + (-40964 : Int) * (-40964 : Int) + (-400291262883853873570153947875132429455025223067014472237276752790342327682 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int) =
        (407405153332789281129834882431923018387634784368827950607958599389691014119 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) - (3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) + (-3165370243326240153920240974391358389351165741312159137315863624924664380 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1910096758335463814148690304927784567117063602611275147333593907816339921721 : Int) =
        (407405153332789281129834882431923018387634784368827950607958599389691014119 : Int) * ((3247695854547107748213455149549234035978018092181694894252872548824707302566 : Int) - (28351713828157723238237498368422776453633195243955962703556456885277541961457 : Int)) - (13074162549871009910548949283150339436620277388484112828409316766144365683819 : Int) + (195047880056353377638579093472229082285592255540804570043936343347192095313 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (22740435912420218396195219097155762916585568462591861465268 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (22740435912420218396195219097155762916585568462591861465268 : Nat) = 11370217956210109198097609548577881458292784231295930732634 + 11370217956210109198097609548577881458292784231295930732634 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
#check @outX
#print axioms outX

set_option pp.all true in
#check @outY
#print axioms outY

set_option pp.all true in
#check @next_double
#print axioms next_double

set_option pp.all true in
#check @prefix_image
#print axioms prefix_image
end ShielddSecurity.ConcretePointTraceStep193
