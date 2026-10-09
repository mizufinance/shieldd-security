import ShielddSecurity.ConcretePointTraceStep020
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep021
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 26685049616425729967417054853767827740913623562056978350507063453246526208038
def inputY : F := 39550046607826240993394033592819401558175799121462689217124476977557117580830
def doubleX : F := 45075071629579103979709597661051208730005034655346913560918799321377977692282
def doubleY : F := 27244255409326297301607472459222489626730770229053008712455863048007091096457
def doubleSlope : F := 15620226294054369468223027820353820520201440224981686539557031588181455241698
def addX : F := 48729963439747569481026778906047914116475299456273893559552974666925363753639
def addY : F := 37742825584509623287984469049684445162014008606354774621860369387940812796195
def addSlope : F := 27055550304955529399953415799369432098948170434102827868786903640734162748483
def outX : F := 48729963439747569481026778906047914116475299456273893559552974666925363753639
def outY : F := 37742825584509623287984469049684445162014008606354774621860369387940812796195

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1899369 : Nat) • base) + ((1899369 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep020.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (39550046607826240993394033592819401558175799121462689217124476977557117580830 : Int)) * (38816428837765773297206624421898982102697416042793854879509777356980227932819 : Int) =
        (1 : Int) + (58555008934465156776172336310827534239866353383764077134842070159667489382003 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (15620226294054369468223027820353820520201440224981686539557031588181455241698 : Int) * ((2 : Int) * (39550046607826240993394033592819401558175799121462689217124476977557117580830 : Int)) =
        (3 : Int) * (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) + (-40964 : Int) * (-40964 : Int) + (-17177443118395607533713388708510901543570716929321104496947336232130441815460 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int) =
        (15620226294054369468223027820353820520201440224981686539557031588181455241698 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) - (26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) + (-4653140024126245915369663084164368240594166313712511615680237881361760545478 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (27244255409326297301607472459222489626730770229053008712455863048007091096457 : Int) =
        (15620226294054369468223027820353820520201440224981686539557031588181455241698 : Int) * ((26685049616425729967417054853767827740913623562056978350507063453246526208038 : Int) - (45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int)) - (39550046607826240993394033592819401558175799121462689217124476977557117580830 : Int) + (5478239934752947519487967575917496897506301298198306063425026626330663964623 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1899369 : Nat) • base) + ((1899369 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (35560291562204880229273451448328003489468063758481435396461418784629081601521 : Int) =
        (1 : Int) + (3658617318344185264208285416598756930801203211707331014028503062112122793206 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (27055550304955529399953415799369432098948170434102827868786903640734162748483 : Int) * ((45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (27244255409326297301607472459222489626730770229053008712455863048007091096457 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (2783607798318768368725234883825755357503451227754426337429777602565369287062 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int) =
        (27055550304955529399953415799369432098948170434102827868786903640734162748483 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-13959961569425976986531269298849587105159313364704054601263775017372848594781 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (37742825584509623287984469049684445162014008606354774621860369387940812796195 : Int) =
        (27055550304955529399953415799369432098948170434102827868786903640734162748483 : Int) * ((45075071629579103979709597661051208730005034655346913560918799321377977692282 : Int) - (48729963439747569481026778906047914116475299456273893559552974666925363753639 : Int)) - (27244255409326297301607472459222489626730770229053008712455863048007091096457 : Int) + (1885829289564154203352319855218432197003095965718021046112078211143335051891 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3798739 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3798739 : Nat) = 1899369 + 1899369 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep021
