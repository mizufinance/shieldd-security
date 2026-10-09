import ShielddSecurity.ConcretePointTraceStep082
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep083
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 30528867951713540512048687902432589990364788194140891424918383835404655526180
def inputY : F := 1312794557321096679255480179769140058270383445927890526788999230382539141520
def doubleX : F := 4359364934139011398398602028115810999270702905806688318175613247952837588276
def doubleY : F := 34539296073793942182712720000190942190348934732191048260365701598514672611898
def doubleSlope : F := 6060593057679948317315761053281253245259422289789548302883513626548514094670
def addX : F := 41563599201413627549918984709942676221534178397299148638277086857557536743764
def addY : F := 28078021518674186043865099631687949879699115245450967847538986726666947435736
def addSlope : F := 41049883942069071796925277586267590564971448485772647496928988840536913011860
def outX : F := 41563599201413627549918984709942676221534178397299148638277086857557536743764
def outY : F := 28078021518674186043865099631687949879699115245450967847538986726666947435736

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((8759297294429794443932573 : Nat) • base) + ((8759297294429794443932573 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep082.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (1312794557321096679255480179769140058270383445927890526788999230382539141520 : Int)) * (3506490605142259324353945461520400898064088277075628413433082959612990068650 : Int) =
        (1 : Int) + (175578333206192684999735526535527760476138697040657386154913444169310319423 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (6060593057679948317315761053281253245259422289789548302883513626548514094670 : Int) * ((2 : Int) * (1312794557321096679255480179769140058270383445927890526788999230382539141520 : Int)) =
        (3 : Int) * (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) + (-40964 : Int) * (-40964 : Int) + (-53019477577018914461569259093670744999172717942593226417091700523289576333632 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int) =
        (6060593057679948317315761053281253245259422289789548302883513626548514094670 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) - (30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) + (-700489656902345965772184864805973880794461337877062872873219263512759363664 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (34539296073793942182712720000190942190348934732191048260365701598514672611898 : Int) =
        (6060593057679948317315761053281253245259422289789548302883513626548514094670 : Int) * ((30528867951713540512048687902432589990364788194140891424918383835404655526180 : Int) - (4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int)) - (1312794557321096679255480179769140058270383445927890526788999230382539141520 : Int) + (-3024698410802580096831150303128151646145096390629697266477970164460755001174 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((8759297294429794443932573 : Nat) • base) + ((8759297294429794443932573 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (13245428514698498104983817559669557510757304852595970148105187797752850148520 : Int) =
        (1 : Int) + (-8922131002992835854113814536366420399414763718668466565193367397242842336857 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (41049883942069071796925277586267590564971448485772647496928988840536913011860 : Int) * ((4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (34539296073793942182712720000190942190348934732191048260365701598514672611898 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-27651233916846149957502739611569833366635833566760839427964928119433930856444 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int) =
        (41049883942069071796925277586267590564971448485772647496928988840536913011860 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-32136261024145001269593213221698732761449014775870633996683747616191137773565 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (28078021518674186043865099631687949879699115245450967847538986726666947435736 : Int) =
        (41049883942069071796925277586267590564971448485772647496928988840536913011860 : Int) * ((4359364934139011398398602028115810999270702905806688318175613247952837588276 : Int) - (41563599201413627549918984709942676221534178397299148638277086857557536743764 : Int)) - (34539296073793942182712720000190942190348934732191048260365701598514672611898 : Int) + (29125660508659504488050345146629368581893577118822559391936992899859761484178 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (17518594588859588887865147 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (17518594588859588887865147 : Nat) = 8759297294429794443932573 + 8759297294429794443932573 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep083
