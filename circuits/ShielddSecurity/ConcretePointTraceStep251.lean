import ShielddSecurity.ConcretePointTraceStep250
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep251
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 41334362864534015912584928801566269682090065139862152751704272394126511954464
def inputY : F := 42626622320796312627407042081663664036453466781731634990546728550724620397934
def doubleX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def doubleY : F := 9391075407031463118118496009339693172461163710862093597958435263695610033367
def doubleSlope : F := 31609886775034648895072828585246440498434754500536143529839840312406629519722

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) • base) + ((3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep250.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (42626622320796312627407042081663664036453466781731634990546728550724620397934 : Int)) * (19920954259600519166657780401982167301463596937282692888173208870782035367876 : Int) =
        (1 : Int) + (32388626704819990786153318923806451103805631094823728632307603940800487707759 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (31609886775034648895072828585246440498434754500536143529839840312406629519722 : Int) * ((2 : Int) * (42626622320796312627407042081663664036453466781731634990546728550724620397934 : Int)) =
        (3 : Int) * (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) + (-40964 : Int) * (-40964 : Int) + (-46356492416834808246584957326914051636987550302373975146254938679288933035768 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) =
        (31609886775034648895072828585246440498434754500536143529839840312406629519722 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) - (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) + (-19055368840386781811642398917828897833585576265924540352322498177988730184857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (9391075407031463118118496009339693172461163710862093597958435263695610033367 : Int) =
        (31609886775034648895072828585246440498434754500536143529839840312406629519722 : Int) * ((41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) - (42626622320796312627407042081663664036453466781731634990546728550724620397934 : Int) + (-997171093875674595510947659653488765063759543655894833551201264346447748637 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem final_add : (((3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) • base) + ((3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) • base)) + base = 0 := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have same : doubleX = baseX := rfl
  have opposite : doubleY = -baseY := by
    have integer : (9391075407031463118118496009339693172461163710862093597958435263695610033367 : Int) =
        -(43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope] using equal
  rw [doubled]
  exact ConcretePointOperationRows01.vertical_addition doubleValid ConcretePointOperationPilot01.base_valid same opposite

theorem scalar_zero : (6554484396890773809930967563523245729705921265872317281365359162392183254199 : Nat) • base = 0 := by
  simpa only [show (6554484396890773809930967563523245729705921265872317281365359162392183254199 : Nat) = 3277242198445386904965483781761622864852960632936158640682679581196091627099 + 3277242198445386904965483781761622864852960632936158640682679581196091627099 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using final_add

end ShielddSecurity.ConcretePointTraceStep251
