import ShielddSecurity.ConcretePointTraceStep025
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep026
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 3282269324988528325038993226636785597530619733789972828218290262497888718808
def inputY : F := 30852909997361908207513808641016876165434383588893462061390256803927125673339
def doubleX : F := 26646125821029640816938003668264446285144635778162256038640849538613754778120
def doubleY : F := 47289273917949842300636236880163842886830619436413642366737398613154902095720
def doubleSlope : F := 7077307418177535433350803993403771313291540465670419776828803720533778766880
def addX : F := 41785182126575712996733242626911863401428220456880171445506002596551360092913
def addY : F := 15764918051038113141343348741325440748789022200505035532985270659576151598433
def addSlope : F := 46242763321819013444923912417903274220428803125738712799715156731377762924104
def outX : F := 41785182126575712996733242626911863401428220456880171445506002596551360092913
def outY : F := 15764918051038113141343348741325440748789022200505035532985270659576151598433

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((60779834 : Nat) • base) + ((60779834 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep025.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (30852909997361908207513808641016876165434383588893462061390256803927125673339 : Int)) * (9753958269847980778001058139000955073397923027760047270141199451202673418391 : Int) =
        (1 : Int) + (11478324548319866951870827833525637543719278746574789156919796773159335474969 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (7077307418177535433350803993403771313291540465670419776828803720533778766880 : Int) * ((2 : Int) * (30852909997361908207513808641016876165434383588893462061390256803927125673339 : Int)) =
        (3 : Int) * (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) + (-40964 : Int) * (-40964 : Int) + (7712108942160540823459147676973717031679051593350722044902501871105484992880 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int) =
        (7077307418177535433350803993403771313291540465670419776828803720533778766880 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) - (3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) + (-955229222819398314147512954259427321629123230926538809065757274715422544464 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (47289273917949842300636236880163842886830619436413642366737398613154902095720 : Int) =
        (7077307418177535433350803993403771313291540465670419776828803720533778766880 : Int) * ((3282269324988528325038993226636785597530619733789972828218290262497888718808 : Int) - (26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int)) - (30852909997361908207513808641016876165434383588893462061390256803927125673339 : Int) + (3153436351437214889864078475880292921980181567778497304518444831432182760163 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((60779834 : Nat) • base) + ((60779834 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (23320225525325880287625881984378707623520188834365927301597173866471827649072 : Int) =
        (1 : Int) + (-5796752992230527910975839418837171043890692219889278989889426189327475218449 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (46242763321819013444923912417903274220428803125738712799715156731377762924104 : Int) * ((26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (47289273917949842300636236880163842886830619436413642366737398613154902095720 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-11494651986261894960822321652570502069868025295367996460105490979949561538902 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int) =
        (46242763321819013444923912417903274220428803125738712799715156731377762924104 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-40781109354920262396105403824153953730993761342079549269144904599536658866236 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (15764918051038113141343348741325440748789022200505035532985270659576151598433 : Int) =
        (46242763321819013444923912417903274220428803125738712799715156731377762924104 : Int) * ((26646125821029640816938003668264446285144635778162256038640849538613754778120 : Int) - (41785182126575712996733242626911863401428220456880171445506002596551360092913 : Int)) - (47289273917949842300636236880163842886830619436413642366737398613154902095720 : Int) + (13351008165973154199529984470969426002280684006606808275889377453365354988625 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (121559669 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (121559669 : Nat) = 60779834 + 60779834 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep026
