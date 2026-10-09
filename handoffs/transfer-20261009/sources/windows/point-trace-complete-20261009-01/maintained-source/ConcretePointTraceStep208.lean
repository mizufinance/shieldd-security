import ShielddSecurity.ConcretePointTraceStep207
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep208
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 12954120461571035702056171298567756350964949136324326159491759066112627428829
def inputY : F := 16082073374785284076261377653680591689523014299702631643648308234993077310527
def doubleX : F := 22863351179066249009209557480531477319560432304432012505803065596432685956083
def doubleY : F := 52064817955487633640026256900029767420450573510049843381448148343257134611
def doubleSlope : F := 19381092106781886436464435777620651280678607874829841225301070402118530374633
def addX : F := 26916134465130630209421683523654143369306760625496507311075300474033539114514
def addY : F := 48301988362936266024813782975498295120488919279325022034506959737919768484464
def addSlope : F := 39280107470796408408257696849178605886078503392824503875194556781546436947179
def outX : F := 26916134465130630209421683523654143369306760625496507311075300474033539114514
def outY : F := 48301988362936266024813782975498295120488919279325022034506959737919768484464

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((372579301989092858203262469687800019625337953691105058246953328 : Nat) • base) + ((372579301989092858203262469687800019625337953691105058246953328 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep207.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (16082073374785284076261377653680591689523014299702631643648308234993077310527 : Int)) * (16372178869426382524842749317831907102811614256514282879515592789595433873975 : Int) =
        (1 : Int) + (10042688560221617949703522349704614925174199169346560234807866840721276915473 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (19381092106781886436464435777620651280678607874829841225301070402118530374633 : Int) * ((2 : Int) * (16082073374785284076261377653680591689523014299702631643648308234993077310527 : Int)) =
        (3 : Int) * (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) + (-40964 : Int) * (-40964 : Int) + (2287528900589339573852862775033649940916529315784566036661722580092846469139 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int) =
        (19381092106781886436464435777620651280678607874829841225301070402118530374633 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) - (12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) + (-7163544615152104595156663486644670908437956226965684179702408839951811060332 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (52064817955487633640026256900029767420450573510049843381448148343257134611 : Int) =
        (19381092106781886436464435777620651280678607874829841225301070402118530374633 : Int) * ((12954120461571035702056171298567756350964949136324326159491759066112627428829 : Int) - (22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int)) - (16082073374785284076261377653680591689523014299702631643648308234993077310527 : Int) + (3662601465155480784419823231169445411011781153174453968719016379368060554840 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((372579301989092858203262469687800019625337953691105058246953328 : Nat) • base) + ((372579301989092858203262469687800019625337953691105058246953328 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (603584088686398249326862888647221231818509186115798229455525667112617405529 : Int) =
        (1 : Int) + (-193577188245330450867656283948526599198742231944560818500067543809346092577 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (39280107470796408408257696849178605886078503392824503875194556781546436947179 : Int) * ((22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (52064817955487633640026256900029767420450573510049843381448148343257134611 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-12597636188056985211597408170570656723748252911905937281411473030204549759305 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int) =
        (39280107470796408408257696849178605886078503392824503875194556781546436947179 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-29425023188117364322212112093081063847860656803207801462154928240281966974633 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (48301988362936266024813782975498295120488919279325022034506959737919768484464 : Int) =
        (39280107470796408408257696849178605886078503392824503875194556781546436947179 : Int) * ((22863351179066249009209557480531477319560432304432012505803065596432685956083 : Int) - (26916134465130630209421683523654143369306760625496507311075300474033539114514 : Int)) - (52064817955487633640026256900029767420450573510049843381448148343257134611 : Int) + (3035970363816345075686985783293353014255546257023679683563037435445877952248 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (745158603978185716406524939375600039250675907382210116493906657 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (745158603978185716406524939375600039250675907382210116493906657 : Nat) = 372579301989092858203262469687800019625337953691105058246953328 + 372579301989092858203262469687800019625337953691105058246953328 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep208
