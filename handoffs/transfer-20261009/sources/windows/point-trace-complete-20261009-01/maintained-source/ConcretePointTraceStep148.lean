import ShielddSecurity.ConcretePointTraceStep147
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep148
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3623301025167337499878569733857069475992406992412737668849808865328299930740
def inputY : F := 43979398470855163907982139051870234426029612511068740011282119168703488597491
def doubleX : F := 9713550031804157378479984726692452399467044512294599631164134919103413305804
def doubleY : F := 13866896872835219272295021648910510678024251940241028617742554881664129604449
def doubleSlope : F := 4757027988805759298089172389227042567804841945280287308162442429179963445096
def addX : F := 6344755949005947150653169382720144082682033786605102380658736430677447133350
def addY : F := 37902207718273805376544761773145242753796073241080595342964531779783224627171
def addSlope : F := 39209724246298421909152547642845241068209953686552698162273267146661543491036
def outX : F := 6344755949005947150653169382720144082682033786605102380658736430677447133350
def outY : F := 37902207718273805376544761773145242753796073241080595342964531779783224627171

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((323161030911765840247017239010400585877186592 : Nat) • base) + ((323161030911765840247017239010400585877186592 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep147.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (43979398470855163907982139051870234426029612511068740011282119168703488597491 : Int)) * (20890979623060311173183895988825371518457555592156992537670848936904820540610 : Int) =
        (1 : Int) + (35043668641766841608929933403025634799973568109731637461339550650451509541963 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (4757027988805759298089172389227042567804841945280287308162442429179963445096 : Int) * ((2 : Int) * (43979398470855163907982139051870234426029612511068740011282119168703488597491 : Int)) =
        (3 : Int) * (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) + (-40964 : Int) * (-40964 : Int) + (7228591621490948756100358498711760630368745888128196943270028618874925422832 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int) =
        (4757027988805759298089172389227042567804841945280287308162442429179963445096 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) - (3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) + (-431561697229303624994134705908842601285264849271055779777993336562020446100 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (13866896872835219272295021648910510678024251940241028617742554881664129604449 : Int) =
        (4757027988805759298089172389227042567804841945280287308162442429179963445096 : Int) * ((3623301025167337499878569733857069475992406992412737668849808865328299930740 : Int) - (9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int)) - (43979398470855163907982139051870234426029612511068740011282119168703488597491 : Int) + (552512662115553272843115995109346358128577000676331746594941359789396872468 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((323161030911765840247017239010400585877186592 : Nat) • base) + ((323161030911765840247017239010400585877186592 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (26272197289567198092345422513311377401179422567623535226394789532036539456738 : Int) =
        (1 : Int) + (-15014339670861722502021302751260659550746130243551879326268587705269375610031 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (39209724246298421909152547642845241068209953686552698162273267146661543491036 : Int) * ((9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (13866896872835219272295021648910510678024251940241028617742554881664129604449 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-22408027457548275188080962103080134551747874799639026016787341151875215068219 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int) =
        (39209724246298421909152547642845241068209953686552698162273267146661543491036 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-29319668458591002949341412900367010432290483568483348139872351897582617535379 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (37902207718273805376544761773145242753796073241080595342964531779783224627171 : Int) =
        (39209724246298421909152547642845241068209953686552698162273267146661543491036 : Int) * ((9713550031804157378479984726692452399467044512294599631164134919103413305804 : Int) - (6344755949005947150653169382720144082682033786605102380658736430677447133350 : Int)) - (13866896872835219272295021648910510678024251940241028617742554881664129604449 : Int) + (-2519067081228739208783796906496902225913902664533818308918850964422650875748 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (646322061823531680494034478020801171754373185 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (646322061823531680494034478020801171754373185 : Nat) = 323161030911765840247017239010400585877186592 + 323161030911765840247017239010400585877186592 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep148
