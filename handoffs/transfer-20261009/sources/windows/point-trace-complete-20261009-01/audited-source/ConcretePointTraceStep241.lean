import ShielddSecurity.ConcretePointTraceStep240
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep241
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 4301177741527633080429491099331482822438211492936113279017635361498379141321
def inputY : F := 21506660964115946440739536739577060615607286387990367006627659911284871509256
def doubleX : F := 89379641616170121796065723130095101348890920562615804044672742520835060320
def doubleY : F := 39192056332735564784666544015465958102667304121424890475019563120539702471841
def doubleSlope : F := 50799794581594702360130970133679648717783570699640162834795031418684781917711
def addX : F := 5662833352520234119656012538123274397754530599769795687764545896965844772978
def addY : F := 14539788680085699392283015300711804488774124497474672376552987941847752158441
def addSlope : F := 42833997100408678603396501551511822424474891961642065635536916439399915401274
def outX : F := 5662833352520234119656012538123274397754530599769795687764545896965844772978
def outY : F := 14539788680085699392283015300711804488774124497474672376552987941847752158441

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) • base) + ((3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep240.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (21506660964115946440739536739577060615607286387990367006627659911284871509256 : Int)) * (563683351211101274859616751944289895800697613742111046027730304104815036058 : Int) =
        (1 : Int) + (462391318353147952342660115827335015073093176578752399069090426487532826015 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (50799794581594702360130970133679648717783570699640162834795031418684781917711 : Int) * ((2 : Int) * (21506660964115946440739536739577060615607286387990367006627659911284871509256 : Int)) =
        (3 : Int) * (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) + (-40964 : Int) * (-40964 : Int) + (40612796510426888426712996295927304826262559743874413051970297768388876028413 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (89379641616170121796065723130095101348890920562615804044672742520835060320 : Int) =
        (50799794581594702360130970133679648717783570699640162834795031418684781917711 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) - (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) + (-49214762238895120082860317677578971181032478760255232900825068819627799109879 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (39192056332735564784666544015465958102667304121424890475019563120539702471841 : Int) =
        (50799794581594702360130970133679648717783570699640162834795031418684781917711 : Int) * ((4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) - (89379641616170121796065723130095101348890920562615804044672742520835060320 : Int)) - (21506660964115946440739536739577060615607286387990367006627659911284871509256 : Int) + (-4080383469906265244475971226114682594856320362109475263429607771360299441278 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) • base) + ((3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((89379641616170121796065723130095101348890920562615804044672742520835060320 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (12895806803352605764656860010662090517831885994160895017864746568152783281712 : Int) =
        (1 : Int) + (-9736763550628249657314069052841839163281336988489542726896646613271183334289 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (42833997100408678603396501551511822424474891961642065635536916439399915401274 : Int) * ((89379641616170121796065723130095101348890920562615804044672742520835060320 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (39192056332735564784666544015465958102667304121424890475019563120539702471841 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-32341094128872062298356775628888042918033092921373816076276560076845436854789 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int) =
        (42833997100408678603396501551511822424474891961642065635536916439399915401274 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (89379641616170121796065723130095101348890920562615804044672742520835060320 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-34990382089935311795501352455170926782999597870784517059722406719632095169351 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (14539788680085699392283015300711804488774124497474672376552987941847752158441 : Int) =
        (42833997100408678603396501551511822424474891961642065635536916439399915401274 : Int) * ((89379641616170121796065723130095101348890920562615804044672742520835060320 : Int) - (5662833352520234119656012538123274397754530599769795687764545896965844772978 : Int)) - (39192056332735564784666544015465958102667304121424890475019563120539702471841 : Int) + (4552861934597282882307275065893450675526796446215807523424195343958583671198 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (6400863668838646298760710511253169657915938736203434845083358557023616459 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (6400863668838646298760710511253169657915938736203434845083358557023616459 : Nat) = 3200431834419323149380355255626584828957969368101717422541679278511808229 + 3200431834419323149380355255626584828957969368101717422541679278511808229 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep241
