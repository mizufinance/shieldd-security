import ShielddSecurity.ConcretePointTraceStep165
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep166
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 32149525223119013181030590267100696338684734941940479540715208589395925388380
def inputY : F := 8242828718938693945061892169048049408741197662909424463389269845496230564948
def doubleX : F := 31520101102725783935204193735625748357051036600606356108215295550034030650280
def doubleY : F := 12290879451489358854826872957033580560610287401604831589909675361892845287554
def doubleSlope : F := 19356494525483276761886602110653189745009215312904595038365849812699837553492
def outX : F := 31520101102725783935204193735625748357051036600606356108215295550034030650280
def outY : F := 12290879451489358854826872957033580560610287401604831589909675361892845287554

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((84714725287333944425714087103142451184189202124595 : Nat) • base) + ((84714725287333944425714087103142451184189202124595 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep165.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (8242828718938693945061892169048049408741197662909424463389269845496230564948 : Int)) * (1329783220133608908050237998051176105808329488585820079018654110308404116044 : Int) =
        (1 : Int) + (418079236029599002554288425298799486585256034396356558294087788283618927071 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19356494525483276761886602110653189745009215312904595038365849812699837553492 : Int) * ((2 : Int) * (8242828718938693945061892169048049408741197662909424463389269845496230564948 : Int)) =
        (3 : Int) * (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) + (-40964 : Int) * (-40964 : Int) + (-53049012131109839934960746200448483924537358662859084085388616630686493404768 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int) =
        (19356494525483276761886602110653189745009215312904595038365849812699837553492 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) - (32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) + (-7145372878086274557673585216490715580495379527592538350219443260788778768184 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (12290879451489358854826872957033580560610287401604831589909675361892845287554 : Int) =
        (19356494525483276761886602110653189745009215312904595038365849812699837553492 : Int) * ((32149525223119013181030590267100696338684734941940479540715208589395925388380 : Int) - (31520101102725783935204193735625748357051036600606356108215295550034030650280 : Int)) - (8242828718938693945061892169048049408741197662909424463389269845496230564948 : Int) + (-232349407727213518592807401821437156826787456581844150309899609586737842746 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (169429450574667888851428174206284902368378404249190 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (169429450574667888851428174206284902368378404249190 : Nat) = 84714725287333944425714087103142451184189202124595 + 84714725287333944425714087103142451184189202124595 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep166
