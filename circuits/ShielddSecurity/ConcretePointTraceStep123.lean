import ShielddSecurity.ConcretePointTraceStep122
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep123
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 20368257134819937805971843041817577931024057560191165555032222071749816904024
def inputY : F := 39833293445309375907166576289695680300022067106281976593773143118549020884056
def doubleX : F := 4943177486272274119331879730300113294250427351211954246019216143541079443262
def doubleY : F := 32362558564332938204842363969659599991755105398382129018648785744185269053974
def doubleSlope : F := 1729982726168751955611818356577766587614864390747620396463228215497286464012
def outX : F := 4943177486272274119331879730300113294250427351211954246019216143541079443262
def outY : F := 32362558564332938204842363969659599991755105398382129018648785744185269053974

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((9630949226372416026801384657931345280 : Nat) • base) + ((9630949226372416026801384657931345280 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep122.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (39833293445309375907166576289695680300022067106281976593773143118549020884056 : Int)) * (16232821447593473251706317388270581882216357343097285648821341875212232339287 : Int) =
        (1 : Int) + (24662761439863636265431992182331772919639523287450440011574836436570387010511 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (1729982726168751955611818356577766587614864390747620396463228215497286464012 : Int) * ((2 : Int) * (39833293445309375907166576289695680300022067106281976593773143118549020884056 : Int)) =
        (3 : Int) * (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) + (-40964 : Int) * (-40964 : Int) + (-21107226174072796732902899819202156824019023558730948481001728572985803689232 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int) =
        (1729982726168751955611818356577766587614864390747620396463228215497286464012 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) - (20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) + (-57076194930412249765591613226897014144154158247953894930775944393011664554 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (32362558564332938204842363969659599991755105398382129018648785744185269053974 : Int) =
        (1729982726168751955611818356577766587614864390747620396463228215497286464012 : Int) * ((20368257134819937805971843041817577931024057560191165555032222071749816904024 : Int) - (4943177486272274119331879730300113294250427351211954246019216143541079443262 : Int)) - (39833293445309375907166576289695680300022067106281976593773143118549020884056 : Int) + (-508909620610721540659107667363410122895633746321994056622463592952697816778 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (19261898452744832053602769315862690560 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (19261898452744832053602769315862690560 : Nat) = 9630949226372416026801384657931345280 + 9630949226372416026801384657931345280 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep123
