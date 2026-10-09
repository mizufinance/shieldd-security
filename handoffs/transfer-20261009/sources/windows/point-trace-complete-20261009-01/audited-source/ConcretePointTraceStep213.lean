import ShielddSecurity.ConcretePointTraceStep212
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep213
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 51890632644277170572261754101000594571566056482089671655303449157124077982639
def inputY : F := 33408851908855639885326291238683177350610626014314456718432505414487450390253
def doubleX : F := 40141994731375510680170207217659938682948621541299614742484231724326413848765
def doubleY : F := 30188904847856880572681052366410206211013291543991729439812232218539759250379
def doubleSlope : F := 37878845828150644818294277999342920619804147798993379823667578426156317767958
def addX : F := 39682198076745101127618121360848096854785234192298571090071992487594601234210
def addY : F := 43542419052801681150733911933397873859937677169140860421067672362058738362163
def addSlope : F := 125513686784436174774162036881640775550329250393818429051023729524908137030
def outX : F := 39682198076745101127618121360848096854785234192298571090071992487594601234210
def outY : F := 43542419052801681150733911933397873859937677169140860421067672362058738362163

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((11922537663650971462504399030009600628010814518115361863902506524 : Nat) • base) + ((11922537663650971462504399030009600628010814518115361863902506524 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep212.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33408851908855639885326291238683177350610626014314456718432505414487450390253 : Int)) * (24432652282397873859358185241788747744356443933286656083863831386982464938799 : Int) =
        (1 : Int) + (31133908192321113988064742038529344614628252144808443337048739545665272269061 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (37878845828150644818294277999342920619804147798993379823667578426156317767958 : Int) * ((2 : Int) * (33408851908855639885326291238683177350610626014314456718432505414487450390253 : Int)) =
        (3 : Int) * (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) + (-40964 : Int) * (-40964 : Int) + (-105785127999525245478230297106476910118677508181665705941732869429001981722439 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int) =
        (37878845828150644818294277999342920619804147798993379823667578426156317767958 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) - (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) + (-27363078359630955645636686586269421422972567395324075757223439258230751270353 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30188904847856880572681052366410206211013291543991729439812232218539759250379 : Int) =
        (37878845828150644818294277999342920619804147798993379823667578426156317767958 : Int) * ((51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) - (40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int)) - (33408851908855639885326291238683177350610626014314456718432505414487450390253 : Int) + (-8487029971508367338320660966885185679771863495163840042006798704803327436820 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((11922537663650971462504399030009600628010814518115361863902506524 : Nat) • base) + ((11922537663650971462504399030009600628010814518115361863902506524 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (29381001081622751638656955540888394255871966035475502880382191420396492127414 : Int) =
        (1 : Int) + (258747567821093915954033782774053780529186770551903464421184224327517632219 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (125513686784436174774162036881640775550329250393818429051023729524908137030 : Int) * ((40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (30188904847856880572681052366410206211013291543991729439812232218539759250379 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1105352438247748289344604044288614914098183673422933732758439583615829979 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int) =
        (125513686784436174774162036881640775550329250393818429051023729524908137030 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-300437162870022332205771463869954012939391970668155984810218248124634170 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (43542419052801681150733911933397873859937677169140860421067672362058738362163 : Int) =
        (125513686784436174774162036881640775550329250393818429051023729524908137030 : Int) * ((40141994731375510680170207217659938682948621541299614742484231724326413848765 : Int) - (39682198076745101127618121360848096854785234192298571090071992487594601234210 : Int)) - (30188904847856880572681052366410206211013291543991729439812232218539759250379 : Int) + (-1100597121742879629245864567075450956185110459760066096633016723455081316 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (23845075327301942925008798060019201256021629036230723727805013049 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (23845075327301942925008798060019201256021629036230723727805013049 : Nat) = 11922537663650971462504399030009600628010814518115361863902506524 + 11922537663650971462504399030009600628010814518115361863902506524 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep213
