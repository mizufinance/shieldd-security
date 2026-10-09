import ShielddSecurity.ConcretePointTraceStep127
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep128
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 5566504998693056018120894468442780266711582254133704871534628739920391741905
def inputY : F := 38165601816628144877808208430799056635264752371660204897234346514679087085370
def doubleX : F := 45596172519381491962768255056820623148708810998180324175650622631853874496372
def doubleY : F := 23453403055099768675533178844813844421104081826927027766201656293308587462910
def doubleSlope : F := 15213814699839873831799647230827073855809850509194815553959928761995800084808
def outX : F := 45596172519381491962768255056820623148708810998180324175650622631853874496372
def outY : F := 23453403055099768675533178844813844421104081826927027766201656293308587462910

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((308190375243917312857644309053803048970 : Nat) • base) + ((308190375243917312857644309053803048970 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep127.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (38165601816628144877808208430799056635264752371660204897234346514679087085370 : Int)) * (45705150784665338025284837459098603440491843356616237856132862652046548064097 : Int) =
        (1 : Int) + (66533249611668707116646227019516007096854189156405570428808023312615539754483 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15213814699839873831799647230827073855809850509194815553959928761995800084808 : Int) * ((2 : Int) * (38165601816628144877808208430799056635264752371660204897234346514679087085370 : Int)) =
        (3 : Int) * (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) + (-40964 : Int) * (-40964 : Int) + (20374044499546392430548963562185676262690523478066091695755847992990000511933 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int) =
        (15213814699839873831799647230827073855809850509194815553959928761995800084808 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) - (5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) + (-4414156471080713792536413402150655748961265211357555650942508395177257196850 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (23453403055099768675533178844813844421104081826927027766201656293308587462910 : Int) =
        (15213814699839873831799647230827073855809850509194815553959928761995800084808 : Int) * ((5566504998693056018120894468442780266711582254133704871534628739920391741905 : Int) - (45596172519381491962768255056820623148708810998180324175650622631853874496372 : Int)) - (38165601816628144877808208430799056635264752371660204897234346514679087085370 : Int) + (11614261078355061029003862512309841604953517397950180411543212160267273052432 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (616380750487834625715288618107606097940 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (616380750487834625715288618107606097940 : Nat) = 308190375243917312857644309053803048970 + 308190375243917312857644309053803048970 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep128
