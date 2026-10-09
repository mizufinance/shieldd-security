import ShielddSecurity.ConcretePointTraceStep224
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep225
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 35855311103515762529636146932706375161657747231140237833757407643560208830105
def inputY : F := 12992391665349874243395288362958038728209139763959198044342396570649696549698
def doubleX : F := 8918426161918850525194028334097142983252407311040627074001158404611232092833
def doubleY : F := 44151611450677000722626194905491299574901819630501622030526674557204465838150
def doubleSlope : F := 22191324940019138617995243281596518088818420819495267703599822720915458739576
def addX : F := 23355861320268275589718429107220870464586034462132280060957987791523229334545
def addY : F := 29392460099502612399823253730311463111786329509682507332461234893669902030629
def addSlope : F := 33279971448294132574068120249590476576030428342946991285399326474138410020436
def outX : F := 23355861320268275589718429107220870464586034462132280060957987791523229334545
def outY : F := 29392460099502612399823253730311463111786329509682507332461234893669902030629

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((48834714270314379110418018426919324172332296266200522194544666725338 : Nat) • base) + ((48834714270314379110418018426919324172332296266200522194544666725338 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep224.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (12992391665349874243395288362958038728209139763959198044342396570649696549698 : Int)) * (14699832184350488222189257168936884169548428904516345442845303531617284221986 : Int) =
        (1 : Int) + (7284553810387984951230170693786266892773463495183918328470512364566781062535 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22191324940019138617995243281596518088818420819495267703599822720915458739576 : Int) * ((2 : Int) * (12992391665349874243395288362958038728209139763959198044342396570649696549698 : Int)) =
        (3 : Int) * (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) + (-40964 : Int) * (-40964 : Int) + (-62555897496646623249082824250314338011399421364603279788556759656479969680115 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int) =
        (22191324940019138617995243281596518088818420819495267703599822720915458739576 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) - (35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) + (-9391564476587956561318237099180953652682893947243342994309468791015604828277 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44151611450677000722626194905491299574901819630501622030526674557204465838150 : Int) =
        (22191324940019138617995243281596518088818420819495267703599822720915458739576 : Int) * ((35855311103515762529636146932706375161657747231140237833757407643560208830105 : Int) - (8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int)) - (12992391665349874243395288362958038728209139763959198044342396570649696549698 : Int) + (-11399927332469605705332581599697373451016207163851904154392161603353904779448 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((48834714270314379110418018426919324172332296266200522194544666725338 : Nat) • base) + ((48834714270314379110418018426919324172332296266200522194544666725338 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (20553044119729735378390284504140305800101540650691099225210778125461634335700 : Int) =
        (1 : Int) + (-12057552735813649657191446531633034052176814162021475181185690488839694697577 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (33279971448294132574068120249590476576030428342946991285399326474138410020436 : Int) * ((8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (44151611450677000722626194905491299574901819630501622030526674557204465838150 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-19523872398005423959998612959972983192862236548022207870392916931940022898308 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int) =
        (33279971448294132574068120249590476576030428342946991285399326474138410020436 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-21122113360370879981713194729098051921109411623812110014071657540791912715731 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (29392460099502612399823253730311463111786329509682507332461234893669902030629 : Int) =
        (33279971448294132574068120249590476576030428342946991285399326474138410020436 : Int) * ((8918426161918850525194028334097142983252407311040627074001158404611232092833 : Int) - (23355861320268275589718429107220870464586034462132280060957987791523229334545 : Int)) - (44151611450677000722626194905491299574901819630501622030526674557204465838150 : Int) + (9163143139153497374513430293805105992946506927939717319332752551586589128747 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (97669428540628758220836036853838648344664592532401044389089333450677 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (97669428540628758220836036853838648344664592532401044389089333450677 : Nat) = 48834714270314379110418018426919324172332296266200522194544666725338 + 48834714270314379110418018426919324172332296266200522194544666725338 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep225
