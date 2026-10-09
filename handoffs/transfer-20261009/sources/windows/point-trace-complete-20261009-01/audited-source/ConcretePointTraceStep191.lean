import ShielddSecurity.ConcretePointTraceStep190
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep191
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 46232636813242975200694222752947787298657322404722802651857447643735279016707
def inputY : F := 36162959617587609228251872809098995771168515068556859207912079638624736142087
def doubleX : F := 52253798650277697310139585834359226230699571962249574089926213732830734827673
def doubleY : F := 29969684708719470422382889280540094752346402268994215123910829433062399673102
def doubleSlope : F := 23127724582249003310876340303143798594882719046200297154402819940548215781485
def addX : F := 17306150278911727178697492610024885255357294397587939352173410848272835446637
def addY : F := 38542751348941648550757212862335065881563860355045139200178813676439229698953
def addSlope : F := 42507595508824200093261435434317814280667353191314311222598491836942949314242
def outX : F := 17306150278911727178697492610024885255357294397587939352173410848272835446637
def outY : F := 38542751348941648550757212862335065881563860355045139200178813676439229698953

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2842554489052527299524402387144470364573196057823982683158 : Nat) • base) + ((2842554489052527299524402387144470364573196057823982683158 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep190.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36162959617587609228251872809098995771168515068556859207912079638624736142087 : Int)) * (51900105304066728910538104560472934561602050052593229425958937937606436527142 : Int) =
        (1 : Int) + (71586920442965327521399453274662441243849384000514349604256145126354188561939 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (23127724582249003310876340303143798594882719046200297154402819940548215781485 : Int) * ((2 : Int) * (36162959617587609228251872809098995771168515068556859207912079638624736142087 : Int)) =
        (3 : Int) * (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) + (-40964 : Int) * (-40964 : Int) + (-90389188014065877729653545406357875665427331514373017750401967181537835766277 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int) =
        (23127724582249003310876340303143798594882719046200297154402819940548215781485 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) - (46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) + (-10200871875713430996418741473776046653904354285812231716502243984987414570962 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (29969684708719470422382889280540094752346402268994215123910829433062399673102 : Int) =
        (23127724582249003310876340303143798594882719046200297154402819940548215781485 : Int) * ((46232636813242975200694222752947787298657322404722802651857447643735279016707 : Int) - (52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int)) - (36162959617587609228251872809098995771168515068556859207912079638624736142087 : Int) + (2655734688645870995844518446757522511256290040551058065687678585757365614323 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2842554489052527299524402387144470364573196057823982683158 : Nat) • base) + ((2842554489052527299524402387144470364573196057823982683158 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (48831162811433265675615501735585566265667624275083569083316963252174060622722 : Int) =
        (1 : Int) + (11709214002445820852378319874923603110681986860628555428029136404334403151883 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (42507595508824200093261435434317814280667353191314311222598491836942949314242 : Int) * ((52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (29969684708719470422382889280540094752346402268994215123910829433062399673102 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (10192887162328426547776000537706708082236277729258567074418064525855873217448 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int) =
        (42507595508824200093261435434317814280667353191314311222598491836942949314242 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-34459149769258388082162129011750819377039359139261358557535264935262261206003 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (38542751348941648550757212862335065881563860355045139200178813676439229698953 : Int) =
        (42507595508824200093261435434317814280667353191314311222598491836942949314242 : Int) * ((52253798650277697310139585834359226230699571962249574089926213732830734827673 : Int) - (17306150278911727178697492610024885255357294397587939352173410848272835446637 : Int)) - (29969684708719470422382889280540094752346402268994215123910829433062399673102 : Int) + (-28330613267981341157408510675611393666067060220017090729876204965086536017089 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (5685108978105054599048804774288940729146392115647965366317 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (5685108978105054599048804774288940729146392115647965366317 : Nat) = 2842554489052527299524402387144470364573196057823982683158 + 2842554489052527299524402387144470364573196057823982683158 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep191
