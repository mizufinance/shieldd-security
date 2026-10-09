import ShielddSecurity.ConcretePointTraceStep198
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep199
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 36547485582606558598401671945885162598989470817915298856933435255016242542972
def inputY : F := 23838545710886353957359568032953173671398394694985585110808103288504335462039
def doubleX : F := 6000225983164968095050672247352624363814612453511354718062854439499784549251
def doubleY : F := 21978334368632662655140312172811026830530697551260318140032867681277421492146
def doubleSlope : F := 11025556390157205716394232601102741138894378089961743827258723452156937564530
def addX : F := 23583482757384776112905908020534842931740118371752496005305901943570318379491
def addY : F := 8629374278687061807636190405225030541556281048258008138682302097311798496146
def addSlope : F := 41000944655183751298036630607603845237812690196199903797487160208592572621974
def outX : F := 23583482757384776112905908020534842931740118371752496005305901943570318379491
def outY : F := 8629374278687061807636190405225030541556281048258008138682302097311798496146

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((727693949197446988678247011108984413330738190802939566888580 : Nat) • base) + ((727693949197446988678247011108984413330738190802939566888580 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep198.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (23838545710886353957359568032953173671398394694985585110808103288504335462039 : Int)) * (39414469763223805974175083935269680431502538122167859201951706831928151456804 : Int) =
        (1 : Int) + (35837435190427240746934957750101259150302009975397271521451959471926072304247 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (11025556390157205716394232601102741138894378089961743827258723452156937564530 : Int) * ((2 : Int) * (23838545710886353957359568032953173671398394694985585110808103288504335462039 : Int)) =
        (3 : Int) * (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) + (-40964 : Int) * (-40964 : Int) + (-66395185273737332438819934734069795845374500267212725666511849320696136726532 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int) =
        (11025556390157205716394232601102741138894378089961743827258723452156937564530 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) - (36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) + (-2318315338621481180566620266541997930015322022851581248807376082306040279121 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21978334368632662655140312172811026830530697551260318140032867681277421492146 : Int) =
        (11025556390157205716394232601102741138894378089961743827258723452156937564530 : Int) * ((36547485582606558598401671945885162598989470817915298856933435255016242542972 : Int) - (6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int)) - (23838545710886353957359568032953173671398394694985585110808103288504335462039 : Int) + (-6423093581513846434558089897881212945238195657472229875474998148143597882265 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((727693949197446988678247011108984413330738190802939566888580 : Nat) • base) + ((727693949197446988678247011108984413330738190802939566888580 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (43119053513710311803663944440701889771596856314262980809692376556809484859540 : Int) =
        (1 : Int) + (-27695715780844682891421190173642084027542902884536628885779505853922916323137 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (41000944655183751298036630607603845237812690196199903797487160208592572621974 : Int) * ((6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (21978334368632662655140312172811026830530697551260318140032867681277421492146 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-26335237380733502422394473941913290284245053048834447236560859969345522287336 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int) =
        (41000944655183751298036630607603845237812690196199903797487160208592572621974 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-32059681601631537868862328545503208868779937892173778961843733559860138517363 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (8629374278687061807636190405225030541556281048258008138682302097311798496146 : Int) =
        (41000944655183751298036630607603845237812690196199903797487160208592572621974 : Int) * ((6000225983164968095050672247352624363814612453511354718062854439499784549251 : Int) - (23583482757384776112905908020534842931740118371752496005305901943570318379491 : Int)) - (21978334368632662655140312172811026830530697551260318140032867681277421492146 : Int) + (13748795751952206421297976073454017376454183142243492114285302660363520688004 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1455387898394893977356494022217968826661476381605879133777161 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1455387898394893977356494022217968826661476381605879133777161 : Nat) = 727693949197446988678247011108984413330738190802939566888580 + 727693949197446988678247011108984413330738190802939566888580 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep199
