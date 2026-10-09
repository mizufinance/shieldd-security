import ShielddSecurity.ConcretePointTraceStep211
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep212
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 39616757784064212658529686082734329854694375587113872326623701052229305486427
def inputY : F := 10338479386250041285497246485137909591009928583279502863946188197271445088555
def doubleX : F := 51890632644277170572261754101000594571566056482089671655303449157124077982639
def doubleY : F := 33408851908855639885326291238683177350610626014314456718432505414487450390253
def doubleSlope : F := 47952497446631224718374951503452632039849335419681845349090595691579605735927
def outX : F := 51890632644277170572261754101000594571566056482089671655303449157124077982639
def outY : F := 33408851908855639885326291238683177350610626014314456718432505414487450390253

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5961268831825485731252199515004800314005407259057680931951253262 : Nat) • base) + ((5961268831825485731252199515004800314005407259057680931951253262 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep211.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (10338479386250041285497246485137909591009928583279502863946188197271445088555 : Int)) * (5413128280020666743094894200068792662188173718714231719525151964654518841464 : Int) =
        (1 : Int) + (2134550627836874827086132733877024738619859500588748288861326263084990183503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (47952497446631224718374951503452632039849335419681845349090595691579605735927 : Int) * ((2 : Int) * (10338479386250041285497246485137909591009928583279502863946188197271445088555 : Int)) =
        (3 : Int) * (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) + (-40964 : Int) * (-40964 : Int) + (-70885642068665687162316077195665137093979605808037189062907674316034148588657 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int) =
        (47952497446631224718374951503452632039849335419681845349090595691579605735927 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) - (39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) + (-43852457953442375506489208363844576635046876341808041111538569640643542302708 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33408851908855639885326291238683177350610626014314456718432505414487450390253 : Int) =
        (47952497446631224718374951503452632039849335419681845349090595691579605735927 : Int) * ((39616757784064212658529686082734329854694375587113872326623701052229305486427 : Int) - (51890632644277170572261754101000594571566056482089671655303449157124077982639 : Int)) - (10338479386250041285497246485137909591009928583279502863946188197271445088555 : Int) + (11224432717656392735704536401293043067703030933723299527175265528856411094564 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (11922537663650971462504399030009600628010814518115361863902506524 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (11922537663650971462504399030009600628010814518115361863902506524 : Nat) = 5961268831825485731252199515004800314005407259057680931951253262 + 5961268831825485731252199515004800314005407259057680931951253262 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep212
