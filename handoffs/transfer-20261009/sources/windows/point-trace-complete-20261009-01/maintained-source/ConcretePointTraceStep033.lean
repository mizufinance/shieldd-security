import ShielddSecurity.ConcretePointTraceStep032
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep033
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 38181194461775874478356199072964542949872183977958664827468175589256533116719
def inputY : F := 38499690297543201976920611390853219381284318318842412359424883691023049216125
def doubleX : F := 4749021286678471767832384381307310280917206812204760017795093055334620067414
def doubleY : F := 1223315771200188839966132554533601265408562182756525544526723739962911763770
def doubleSlope : F := 43543162291222711328475320137807348136145852796378813553090072922233340889110
def addX : F := 24851920105061636754870529796747350313026361476967296100868617233016623517151
def addY : F := 39527505731992063567627203920232128899227990453209890860340527769887280618093
def addSlope : F := 44925630119760164867367020766296926814309629929025752092666591955990394816170
def outX : F := 24851920105061636754870529796747350313026361476967296100868617233016623517151
def outY : F := 39527505731992063567627203920232128899227990453209890860340527769887280618093

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((7779818828 : Nat) • base) + ((7779818828 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep032.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (38499690297543201976920611390853219381284318318842412359424883691023049216125 : Int)) * (43398483471021523506778975331264465714584671811321943335164193168470027530510 : Int) =
        (1 : Int) + (63728436588008389630741523915362335183795279768049599506264512414723387434923 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (43543162291222711328475320137807348136145852796378813553090072922233340889110 : Int) * ((2 : Int) * (38499690297543201976920611390853219381284318318842412359424883691023049216125 : Int)) =
        (3 : Int) * (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) + (-40964 : Int) * (-40964 : Int) + (-19464046372825813550653584914866431186627985016013259033601958001475946100615 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int) =
        (43543162291222711328475320137807348136145852796378813553090072922233340889110 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) - (38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) + (-36158583717491973961418260499386837734450550664972569357606498065578816773432 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (1223315771200188839966132554533601265408562182756525544526723739962911763770 : Int) =
        (43543162291222711328475320137807348136145852796378813553090072922233340889110 : Int) * ((38181194461775874478356199072964542949872183977958664827468175589256533116719 : Int) - (4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int)) - (38499690297543201976920611390853219381284318318842412359424883691023049216125 : Int) + (-27762338998817432187346211963248807890185636393554098935162956842849430813935 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((7779818828 : Nat) • base) + ((7779818828 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (41139969669152482673769696299216262097408363784885895912097382351454400111209 : Int) =
        (1 : Int) + (-27406200409870015861519512388729930171208923256260738275078632284103832508294 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (44925630119760164867367020766296926814309629929025752092666591955990394816170 : Int) * ((4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (1223315771200188839966132554533601265408562182756525544526723739962911763770 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-29928092619014425666165824446784737308754733628131829450057212770152614522258 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int) =
        (44925630119760164867367020766296926814309629929025752092666591955990394816170 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-38491056646174200535607364852387462544560241583282733669963228339699147832740 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (39527505731992063567627203920232128899227990453209890860340527769887280618093 : Int) =
        (44925630119760164867367020766296926814309629929025752092666591955990394816170 : Int) * ((4749021286678471767832384381307310280917206812204760017795093055334620067414 : Int) - (24851920105061636754870529796747350313026361476967296100868617233016623517151 : Int)) - (1223315771200188839966132554533601265408562182756525544526723739962911763770 : Int) + (17223616343454541928201764956605485030709050771434887242246314001753184837281 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (15559637657 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (15559637657 : Nat) = 7779818828 + 7779818828 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep033
