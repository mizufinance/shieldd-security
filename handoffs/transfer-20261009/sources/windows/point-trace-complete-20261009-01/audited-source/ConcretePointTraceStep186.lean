import ShielddSecurity.ConcretePointTraceStep185
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep186
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 37862255749134806676188635197039702004588675458382753068389397604913765690923
def inputY : F := 7717806057604630173410734524852618806032453212125288469628410750714977513045
def doubleX : F := 18343024213400604444694444970536111620426771053578836669011306779771076370013
def doubleY : F := 33770282746234431365469966205229999106466595454311766934719173189639547408370
def doubleSlope : F := 10274621457795807211368618066711737971799235120304509770862487905372320671440
def addX : F := 20522956576139066457096458101918878226645455583682215137754180798539380984290
def addY : F := 34340343647199510772018322333983488868541239391279071219131531861272583706286
def addSlope : F := 27366495625523615046809624032657228693453464331400507426530650915786457579476
def outX : F := 20522956576139066457096458101918878226645455583682215137754180798539380984290
def outY : F := 34340343647199510772018322333983488868541239391279071219131531861272583706286

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((88829827782891478110137574598264698892912376806999458848 : Nat) • base) + ((88829827782891478110137574598264698892912376806999458848 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep185.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (7717806057604630173410734524852618806032453212125288469628410750714977513045 : Int)) * (52017626598118958769641079941449097097776878497739981184590986278041470308020 : Int) =
        (1 : Int) + (15312491774777060772114989192240773352424505091429073270496090059205267846023 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (10274621457795807211368618066711737971799235120304509770862487905372320671440 : Int) * ((2 : Int) * (7717806057604630173410734524852618806032453212125288469628410750714977513045 : Int)) =
        (3 : Int) * (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) + (-40964 : Int) * (-40964 : Int) + (-78992791594530014059677840986830166590302328263383770771376808611846035507435 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int) =
        (10274621457795807211368618066711737971799235120304509770862487905372320671440 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) - (37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) + (-2013275181322345162676474403380260174754794549739992199717600509572244663893 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33770282746234431365469966205229999106466595454311766934719173189639547408370 : Int) =
        (10274621457795807211368618066711737971799235120304509770862487905372320671440 : Int) * ((37862255749134806676188635197039702004588675458382753068389397604913765690923 : Int) - (18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int)) - (7717806057604630173410734524852618806032453212125288469628410750714977513045 : Int) + (-3824723331248501432913736127944287383675747193704157842922303202246683864345 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((88829827782891478110137574598264698892912376806999458848 : Nat) • base) + ((88829827782891478110137574598264698892912376806999458848 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (32179995751663889733317380751654076522205291379886464461620134480942350694331 : Int) =
        (1 : Int) + (-13094672154263769307660215230357222903409891062057969666147120284857876903667 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (27366495625523615046809624032657228693453464331400507426530650915786457579476 : Int) * ((18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (33770282746234431365469966205229999106466595454311766934719173189639547408370 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-11135964435570079847887224360565942659982447818073730472875839192053079573888 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int) =
        (27366495625523615046809624032657228693453464331400507426530650915786457579476 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-14282684904572126645062040823725816038297582083640841141813318409344323024966 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (34340343647199510772018322333983488868541239391279071219131531861272583706286 : Int) =
        (27366495625523615046809624032657228693453464331400507426530650915786457579476 : Int) * ((18343024213400604444694444970536111620426771053578836669011306779771076370013 : Int) - (20522956576139066457096458101918878226645455583682215137754180798539380984290 : Int)) - (33770282746234431365469966205229999106466595454311766934719173189639547408370 : Int) + (1137715529102464536097883912836787552322679141261628818896099284699367730116 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (177659655565782956220275149196529397785824753613998917697 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (177659655565782956220275149196529397785824753613998917697 : Nat) = 88829827782891478110137574598264698892912376806999458848 + 88829827782891478110137574598264698892912376806999458848 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep186
