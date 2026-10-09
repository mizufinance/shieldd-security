import ShielddSecurity.ConcretePointTraceStep055
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep056
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 31821713574010330538382950101579067928739038575118356086435948515512232693722
def inputY : F := 21428241172033728239026214104476644721006577958178016165697661930459516900527
def doubleX : F := 13480797493210856661199056142696908067610055456934674178268628129211279262521
def doubleY : F := 36262226805641362318929986472431706312144092821703975966412966588116665218769
def doubleSlope : F := 2049862035197716411307073700095751261362736664220440108705187172544154427789
def addX : F := 19335923905674262999057160929532315590043339984859945221466128014705795328784
def addY : F := 50877486256830705277735530352327310548382597972553854693908769095627960436820
def addSlope : F := 44617680960774418997346795466935764497490287461746860147864807705321119246165
def outX : F := 19335923905674262999057160929532315590043339984859945221466128014705795328784
def outY : F := 50877486256830705277735530352327310548382597972553854693908769095627960436820

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((65261850464566010 : Nat) • base) + ((65261850464566010 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep055.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21428241172033728239026214104476644721006577958178016165697661930459516900527 : Int)) * (19298708857526690969690875047594588136547409811335589032493627490225756705823 : Int) =
        (1 : Int) + (15773070872825390095264756871519749040702767860898853533761674236092456655457 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (2049862035197716411307073700095751261362736664220440108705187172544154427789 : Int) * ((2 : Int) * (21428241172033728239026214104476644721006577958178016165697661930459516900527 : Int)) =
        (3 : Int) * (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) + (-40964 : Int) * (-40964 : Int) + (-56259468892000531910112812788678400222429184322873397234461890081059078630550 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int) =
        (2049862035197716411307073700095751261362736664220440108705187172544154427789 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) - (31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) + (-80134723589741471618691646090057279883318373846870149950544791060729726148 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (36262226805641362318929986472431706312144092821703975966412966588116665218769 : Int) =
        (2049862035197716411307073700095751261362736664220440108705187172544154427789 : Int) * ((31821713574010330538382950101579067928739038575118356086435948515512232693722 : Int) - (13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int)) - (21428241172033728239026214104476644721006577958178016165697661930459516900527 : Int) + (-716996663814864150469939396113995821832912383363665582517524949845949590061 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((65261850464566010 : Nat) • base) + ((65261850464566010 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (50065290110462621792309667198584707130144216870323242028741184548383983171430 : Int) =
        (1 : Int) + (-25014958860820042938371497425899416235270958929456498054196664984545561714397 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (44617680960774418997346795466935764497490287461746860147864807705321119246165 : Int) * ((13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (36262226805641362318929986472431706312144092821703975966412966588116665218769 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-22293078722532394312389805233546576990644165110358372564352093367347595708681 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int) =
        (44617680960774418997346795466935764497490287461746860147864807705321119246165 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-37965180282940919500049906790823625048472766161013210694133296901308700077285 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (50877486256830705277735530352327310548382597972553854693908769095627960436820 : Int) =
        (44617680960774418997346795466935764497490287461746860147864807705321119246165 : Int) * ((13480797493210856661199056142696908067610055456934674178268628129211279262521 : Int) - (19335923905674262999057160929532315590043339984859945221466128014705795328784 : Int)) - (36262226805641362318929986472431706312144092821703975966412966588116665218769 : Int) + (4982126480845320531141232824816736247856461072828340428577586554143215237768 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (130523700929132021 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (130523700929132021 : Nat) = 65261850464566010 + 65261850464566010 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep056
