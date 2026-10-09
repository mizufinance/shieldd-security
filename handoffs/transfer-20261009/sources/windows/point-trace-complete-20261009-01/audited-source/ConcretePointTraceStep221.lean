import ShielddSecurity.ConcretePointTraceStep220
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep221
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 5426695565711702682421420025351840595683857721779550813188589146006034759360
def inputY : F := 27176793175848885822729853230278611057591852422142903882448268509402730353669
def doubleX : F := 15057547521266068854831622276010137411789776155338002270350976002537008125760
def doubleY : F := 40788491856879354104456305270247142492702806183488296414493630674807945271787
def doubleSlope : F := 45387100573313770138169057180931481243442776231826801197840386875179933998691
def addX : F := 41166441787998895917461425299633054061526863280062283667716671165737095590783
def addY : F := 33716406380140631984492975456332915229715017469525544957878853284288154815086
def addSlope : F := 34912399031987004289554784618993212304299541040143682975593179605270269238239
def outX : F := 41166441787998895917461425299633054061526863280062283667716671165737095590783
def outY : F := 33716406380140631984492975456332915229715017469525544957878853284288154815086

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3052169641894648694401126151682457760770768516637532637159041670333 : Nat) • base) + ((3052169641894648694401126151682457760770768516637532637159041670333 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep220.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (27176793175848885822729853230278611057591852422142903882448268509402730353669 : Int)) * (42547213773266427209554424308618548722230382265114286121612672150139427975964 : Int) =
        (1 : Int) + (44103271855876220969498928826410884332646206841193632951775055752489783582487 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (45387100573313770138169057180931481243442776231826801197840386875179933998691 : Int) * ((2 : Int) * (27176793175848885822729853230278611057591852422142903882448268509402730353669 : Int)) =
        (3 : Int) * (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) + (-40964 : Int) * (-40964 : Int) + (45362161078306670982315250940145114992785239218264693455869172377464090092494 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int) =
        (45387100573313770138169057180931481243442776231826801197840386875179933998691 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) - (5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) + (-39285868531270140269559881150108518939355207150464531574073525024004140352913 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (40788491856879354104456305270247142492702806183488296414493630674807945271787 : Int) =
        (45387100573313770138169057180931481243442776231826801197840386875179933998691 : Int) * ((5426695565711702682421420025351840595683857721779550813188589146006034759360 : Int) - (15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int)) - (27176793175848885822729853230278611057591852422142903882448268509402730353669 : Int) + (8336209605609765945864603931576245109232992771748031650268086531474072364912 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3052169641894648694401126151682457760770768516637532637159041670333 : Nat) • base) + ((3052169641894648694401126151682457760770768516637532637159041670333 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (1965325028765362225126647714489973785551100706833305958545466436200244508689 : Int) =
        (1 : Int) + (-922870792699553655382739527507592118133525742770492802070499447787509544196 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (34912399031987004289554784618993212304299541040143682975593179605270269238239 : Int) * ((15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (40788491856879354104456305270247142492702806183488296414493630674807945271787 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-16394048260777347149172898995149557928314462591350761363252857193283956496526 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int) =
        (34912399031987004289554784618993212304299541040143682975593179605270269238239 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-23245070328241237514482804296659927009524597792094647889260290731498862008951 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (33716406380140631984492975456332915229715017469525544957878853284288154815086 : Int) =
        (34912399031987004289554784618993212304299541040143682975593179605270269238239 : Int) * ((15057547521266068854831622276010137411789776155338002270350976002537008125760 : Int) - (41166441787998895917461425299633054061526863280062283667716671165737095590783 : Int)) - (40788491856879354104456305270247142492702806183488296414493630674807945271787 : Int) + (17383597239100349453525001518983901613357446427657088109556000132300669330490 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (6104339283789297388802252303364915521541537033275065274318083340667 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (6104339283789297388802252303364915521541537033275065274318083340667 : Nat) = 3052169641894648694401126151682457760770768516637532637159041670333 + 3052169641894648694401126151682457760770768516637532637159041670333 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep221
