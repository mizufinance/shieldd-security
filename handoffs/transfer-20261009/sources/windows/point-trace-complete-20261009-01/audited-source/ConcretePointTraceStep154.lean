import ShielddSecurity.ConcretePointTraceStep153
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep154
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 343511366769113804656546802764779546722161162829979512415871444728095558163
def inputY : F := 44750022144722540566978321980808116286834314338329035391606952686135637804525
def doubleX : F := 9336825872027364196236636847278086903913221079713658086192758548778980867140
def doubleY : F := 8584284756153844106270813348672267237444486423110203881826728990855799929949
def doubleSlope : F := 46084482866363297549407427344128764647324030019409567916407996087151679318399
def addX : F := 50748321365867478650009361082350517714146176131919743463351403407907922312422
def addY : F := 41282394913594334171855457540884645471423541173374508094727234669777023316141
def addSlope : F := 46910343266002026410906500718582972883820802356919958359972490995759342785016
def outX : F := 50748321365867478650009361082350517714146176131919743463351403407907922312422
def outY : F := 41282394913594334171855457540884645471423541173374508094727234669777023316141

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((20682305978353013775809103296665637496139941924 : Nat) • base) + ((20682305978353013775809103296665637496139941924 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep153.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (44750022144722540566978321980808116286834314338329035391606952686135637804525 : Int)) * (12910216273274526471996643551904744333579032626377540509183571300837539322135 : Int) =
        (1 : Int) + (22035770822654225595513306743474731723281211557664425086414086855630205377173 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (46084482866363297549407427344128764647324030019409567916407996087151679318399 : Int) * ((2 : Int) * (44750022144722540566978321980808116286834314338329035391606952686135637804525 : Int)) =
        (3 : Int) * (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) + (-40964 : Int) * (-40964 : Int) + (78652434876776407128776926033658387090441040419801327607764709910114840146955 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int) =
        (46084482866363297549407427344128764647324030019409567916407996087151679318399 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) - (343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) + (-40502414691603768282280034326940477112405000649645734665164191325996719414431 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (8584284756153844106270813348672267237444486423110203881826728990855799929949 : Int) =
        (46084482866363297549407427344128764647324030019409567916407996087151679318399 : Int) * ((343511366769113804656546802764779546722161162829979512415871444728095558163 : Int) - (9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int)) - (44750022144722540566978321980808116286834314338329035391606952686135637804525 : Int) + (7903982661588005979822165215865513416964392040486495139226417283931092009369 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((20682305978353013775809103296665637496139941924 : Nat) • base) + ((20682305978353013775809103296665637496139941924 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (43316357599705504964586299687695364071553643696687633139528899061161303092742 : Int) =
        (1 : Int) + (-25066139088470315825092516285857883467994738025254812050966284011779426398939 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (46910343266002026410906500718582972883820802356919958359972490995759342785016 : Int) * ((9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (8584284756153844106270813348672267237444486423110203881826728990855799929949 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-27145892548488148576268061286457977850885464793061820501048868633748306258107 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int) =
        (46910343266002026410906500718582972883820802356919958359972490995759342785016 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-41967074984151741502904637060558580772543257727446501752181668881266033999883 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (41282394913594334171855457540884645471423541173374508094727234669777023316141 : Int) =
        (46910343266002026410906500718582972883820802356919958359972490995759342785016 : Int) * ((9336825872027364196236636847278086903913221079713658086192758548778980867140 : Int) - (50748321365867478650009361082350517714146176131919743463351403407907922312422 : Int)) - (8584284756153844106270813348672267237444486423110203881826728990855799929949 : Int) + (37047678946647061658099357751990386750143114787520408005372950531626349071354 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (41364611956706027551618206593331274992279883849 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (41364611956706027551618206593331274992279883849 : Nat) = 20682305978353013775809103296665637496139941924 + 20682305978353013775809103296665637496139941924 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep154
