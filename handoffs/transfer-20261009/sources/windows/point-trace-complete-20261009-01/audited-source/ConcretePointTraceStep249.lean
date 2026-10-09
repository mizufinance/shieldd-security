import ShielddSecurity.ConcretePointTraceStep248
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep249
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 11461277467152783638462415397995436491772411768632117744545883083797289909445
def inputY : F := 37938685389307505719446694593178758230543244701943533122566970596180847459634
def doubleX : F := 20969501840203811219873724426750675539772494053906554027915193543823185147275
def doubleY : F := 3636592505858037894778754691837986351979264743789781605722112172603964053081
def doubleSlope : F := 44488304377487300881370215243645265426784343506391909265959408601085110670041
def addX : F := 2831284930826257191850187232551642402086626139799524735967873635909311110677
def addY : F := 32716214748985956159375712475996032039789345680637979423244305125903608692678
def addSlope : F := 5771524387438492391175361575357403227732082041812655195270478136172243354652
def outX : F := 2831284930826257191850187232551642402086626139799524735967873635909311110677
def outY : F := 32716214748985956159375712475996032039789345680637979423244305125903608692678

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) • base) + ((819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep248.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (37938685389307505719446694593178758230543244701943533122566970596180847459634 : Int)) * (2146006962097367161466670678594331773152824972912633172705670331329314084664 : Int) =
        (1 : Int) + (3105380913596227965913570309904146737647457857607515269147479879036196405727 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (44488304377487300881370215243645265426784343506391909265959408601085110670041 : Int) * ((2 : Int) * (37938685389307505719446694593178758230543244701943533122566970596180847459634 : Int)) =
        (3 : Int) * (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) + (-40964 : Int) * (-40964 : Int) + (56861317048058929091515666534521092372263733073208332685835820982176660309049 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int) =
        (44488304377487300881370215243645265426784343506391909265959408601085110670041 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) - (11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) + (-37745326453954673355068273598018998018954375208487845203316605022167699492068 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (3636592505858037894778754691837986351979264743789781605722112172603964053081 : Int) =
        (44488304377487300881370215243645265426784343506391909265959408601085110670041 : Int) * ((11461277467152783638462415397995436491772411768632117744545883083797289909445 : Int) - (20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int)) - (37938685389307505719446694593178758230543244701943533122566970596180847459634 : Int) + (8067087248662851896493524524603872620544010377820901056432845277241307520865 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) • base) + ((819310549611346726241370945440405716213240158234039660170669895299022906774 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (5806797849534752664970505840749790998360328093420982725401352385967265373486 : Int) =
        (1 : Int) + (-2072041478225309546800020459758863337318947243375317834404479701567772413553 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (5771524387438492391175361575357403227732082041812655195270478136172243354652 : Int) * ((20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (3636592505858037894778754691837986351979264743789781605722112172603964053081 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-2059454837801807381202821242444121521139646906795731540242031978606199117327 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) =
        (5771524387438492391175361575357403227732082041812655195270478136172243354652 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-635261519780996024384587707979315695691412456076522313178890157104796674149 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (32716214748985956159375712475996032039789345680637979423244305125903608692678 : Int) =
        (5771524387438492391175361575357403227732082041812655195270478136172243354652 : Int) * ((20969501840203811219873724426750675539772494053906554027915193543823185147275 : Int) - (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int)) - (3636592505858037894778754691837986351979264743789781605722112172603964053081 : Int) + (-1996441575304933589254642104846338730665798540510533420620835291873996559049 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) = 819310549611346726241370945440405716213240158234039660170669895299022906774 + 819310549611346726241370945440405716213240158234039660170669895299022906774 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep249
