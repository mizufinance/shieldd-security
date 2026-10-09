import ShielddSecurity.ConcretePointTraceStep215
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep216
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 2472871116929812212281188731644840928172978252295042402628337375621512375572
def inputY : F := 15626333237137253335437934225429213444962979570757477153778973902077750255117
def doubleX : F := 11477215441076321449968374651813237070227892511540365114078383474981036070643
def doubleY : F := 50455274892921902704224339184681212622628843627692636216400286102884528202349
def doubleSlope : F := 5305765408628606582373817824006083257278707975035587131024807111158300099535
def addX : F := 31807404585560487380869877515858187052475130286902328101832048210678012912779
def addY : F := 48411753480801839013272274296788929974729909911120472290649729964566788389298
def addSlope : F := 75503072917844787349134258690221750821970947473304308322990124626685321611
def outX : F := 31807404585560487380869877515858187052475130286902328101832048210678012912779
def outY : F := 48411753480801839013272274296788929974729909911120472290649729964566788389298

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((95380301309207771700035192240076805024086516144922894911220052197 : Nat) • base) + ((95380301309207771700035192240076805024086516144922894911220052197 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep215.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15626333237137253335437934225429213444962979570757477153778973902077750255117 : Int)) * (25931940170391191629287965591689890976915057998299514442539706896264129844418 : Int) =
        (1 : Int) + (15455873950217266465582968421372645171215300153491829528558104848121838080947 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (5305765408628606582373817824006083257278707975035587131024807111158300099535 : Int) * ((2 : Int) * (15626333237137253335437934225429213444962979570757477153778973902077750255117 : Int)) =
        (3 : Int) * (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) + (-40964 : Int) * (-40964 : Int) + (2812464587102614980802896858377427744930859403848923173973957602777471523718 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int) =
        (5305765408628606582373817824006083257278707975035587131024807111158300099535 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) - (2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) + (-536868059842240192885722841834849351678085585687882504640810877952045994062 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (50455274892921902704224339184681212622628843627692636216400286102884528202349 : Int) =
        (5305765408628606582373817824006083257278707975035587131024807111158300099535 : Int) * ((2472871116929812212281188731644840928172978252295042402628337375621512375572 : Int) - (11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int)) - (15626333237137253335437934225429213444962979570757477153778973902077750255117 : Int) + (911111686090455423182392774939666509603801987461998633494336915293874305227 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((95380301309207771700035192240076805024086516144922894911220052197 : Nat) • base) + ((95380301309207771700035192240076805024086516144922894911220052197 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12065838093966041646457067938770728329551125856011533634494030368865205768821 : Int) =
        (1 : Int) + (-6489693982214732906013819249680480615986110982532132457473163668922161553057 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (75503072917844787349134258690221750821970947473304308322990124626685321611 : Int) * ((11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (50455274892921902704224339184681212622628843627692636216400286102884528202349 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-40609846919684395250380311545186853670186718836775096724603516544700315811 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int) =
        (75503072917844787349134258690221750821970947473304308322990124626685321611 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-108717819641572670990452611847830806740468619572424833614655443608125168 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (48411753480801839013272274296788929974729909911120472290649729964566788389298 : Int) =
        (75503072917844787349134258690221750821970947473304308322990124626685321611 : Int) * ((11477215441076321449968374651813237070227892511540365114078383474981036070643 : Int) - (31807404585560487380869877515858187052475130286902328101832048210678012912779 : Int)) - (50455274892921902704224339184681212622628843627692636216400286102884528202349 : Int) + (29273693788517385106716126499834211934174576484658637932551057050746508711 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (190760602618415543400070384480153610048173032289845789822440104395 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (190760602618415543400070384480153610048173032289845789822440104395 : Nat) = 95380301309207771700035192240076805024086516144922894911220052197 + 95380301309207771700035192240076805024086516144922894911220052197 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep216
