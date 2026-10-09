import ShielddSecurity.ConcretePointTraceStep027
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep028
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 50164002177227998388068244692330561515137937488035730124225134062052445127465
def inputY : F := 30444564358102861213985435358462683215846645980116264891021397328065510099318
def doubleX : F := 11588435951221175233044980985051644150460896435316666909091959764933412287874
def doubleY : F := 15248497707848093284485582568996720271841207247011320331443362226385948315421
def doubleSlope : F := 26384588810483508634867094291569061357603299658640591109476040020564019378330
def outX : F := 11588435951221175233044980985051644150460896435316666909091959764933412287874
def outY : F := 15248497707848093284485582568996720271841207247011320331443362226385948315421

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((243119338 : Nat) • base) + ((243119338 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep027.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (30444564358102861213985435358462683215846645980116264891021397328065510099318 : Int)) * (9703567663863900143256127567120142851960615823526072538640902026383941352498 : Int) =
        (1 : Int) + (11267892039908129149088842619443311411709502845882639946087292052031688147479 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (26384588810483508634867094291569061357603299658640591109476040020564019378330 : Int) * ((2 : Int) * (30444564358102861213985435358462683215846645980116264891021397328065510099318 : Int)) =
        (3 : Int) * (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) + (-40964 : Int) * (-40964 : Int) + (-113333604126133723424070999760317950546792808433037058301522328053295818228027 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int) =
        (26384588810483508634867094291569061357603299658640591109476040020564019378330 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) - (50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) + (-13276149666107222466946327150691398777278278274021892141565583947784374976728 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15248497707848093284485582568996720271841207247011320331443362226385948315421 : Int) =
        (26384588810483508634867094291569061357603299658640591109476040020564019378330 : Int) * ((50164002177227998388068244692330561515137937488035730124225134062052445127465 : Int) - (11588435951221175233044980985051644150460896435316666909091959764933412287874 : Int)) - (30444564358102861213985435358462683215846645980116264891021397328065510099318 : Int) + (-19410383627726220571250150818588329283065482488073712165306743014468967015907 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (486238676 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (486238676 : Nat) = 243119338 + 243119338 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep028
