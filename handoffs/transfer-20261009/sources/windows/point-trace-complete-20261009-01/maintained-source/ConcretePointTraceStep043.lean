import ShielddSecurity.ConcretePointTraceStep042
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep043
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 2773412723143448389350708801469384239684308280547399336978566097928962106716
def inputY : F := 40503156611042317495852284948043867079457983042714828037865598012630344930635
def doubleX : F := 9938142544908115234945408199367279764005038581109170790468914752009458692090
def doubleY : F := 21043747806329552561160832757858922142713440772972389938043837427116821032209
def doubleSlope : F := 40251575829271057233731198154368077533878543548166802421113130168548064836660
def addX : F := 41420983510373286248097911444478048782904202611705300317720624829134874036356
def addY : F := 26916796564446889899868763747739476696533691125895817157306401920241054741533
def addSlope : F := 20508181801028362406702583477099792261145379572798666349287877162425788495390
def outX : F := 41420983510373286248097911444478048782904202611705300317720624829134874036356
def outY : F := 26916796564446889899868763747739476696533691125895817157306401920241054741533

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((7966534480537 : Nat) • base) + ((7966534480537 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep042.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (40503156611042317495852284948043867079457983042714828037865598012630344930635 : Int)) * (45743810765462149010367298722525403462276668772314612821584047816544134939539 : Int) =
        (1 : Int) + (70667981614934041632158729224551937232042148127567515598782310742833963251233 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40251575829271057233731198154368077533878543548166802421113130168548064836660 : Int) * ((2 : Int) * (40503156611042317495852284948043867079457983042714828037865598012630344930635 : Int)) =
        (3 : Int) * (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) + (-40964 : Int) * (-40964 : Int) + (61743153787304916058480042860564595945586326626389823419593091125202720127224 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int) =
        (40251575829271057233731198154368077533878543548166802421113130168548064836660 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) - (2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) + (-30898489847426464806555527890899163092925829051942792530325853604468328378342 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (21043747806329552561160832757858922142713440772972389938043837427116821032209 : Int) =
        (40251575829271057233731198154368077533878543548166802421113130168548064836660 : Int) * ((2773412723143448389350708801469384239684308280547399336978566097928962106716 : Int) - (9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int)) - (40503156611042317495852284948043867079457983042714828037865598012630344930635 : Int) + (5499892292325149695167966368853270180857995127205202687586950979672635863668 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((7966534480537 : Nat) • base) + ((7966534480537 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (24653530734408446059646713696267764288942123453527215206743590241897928424526 : Int) =
        (1 : Int) + (-13983689741836907490596778116253701280591838364535515875936041404652370716063 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (20508181801028362406702583477099792261145379572798666349287877162425788495390 : Int) * ((9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (21043747806329552561160832757858922142713440772972389938043837427116821032209 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-11632413002593312537630688497526731957801002406524469889716442197406888189141 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int) =
        (20508181801028362406702583477099792261145379572798666349287877162425788495390 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-8020949767298677663201224664221809758188836538126896366769378648528794487803 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (26916796564446889899868763747739476696533691125895817157306401920241054741533 : Int) =
        (20508181801028362406702583477099792261145379572798666349287877162425788495390 : Int) * ((9938142544908115234945408199367279764005038581109170790468914752009458692090 : Int) - (41420983510373286248097911444478048782904202611705300317720624829134874036356 : Int)) - (21043747806329552561160832757858922142713440772972389938043837427116821032209 : Int) + (12313245921351577868549018392496433667842419260949928516098734885066492321114 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (15933068961075 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (15933068961075 : Nat) = 7966534480537 + 7966534480537 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep043
