import ShielddSecurity.ConcretePointTraceStep204
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep205
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 16810720316566490990751060652421470777556901491962546143899626636772648017141
def inputY : F := 20066309154940202382437977043853789027233261813845634108541543434177679150734
def doubleX : F := 28814607045722471110364957977252371237120881648332950145347460831244775941807
def doubleY : F := 15814575136589955221349585958799725147342085565011021245672905698170615381466
def doubleSlope : F := 16045425122321928642851222633670103590917318498255667210140514834515367159515
def outX : F := 28814607045722471110364957977252371237120881648332950145347460831244775941807
def outY : F := 15814575136589955221349585958799725147342085565011021245672905698170615381466

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((46572412748636607275407808710975002453167244211388132280869166 : Nat) • base) + ((46572412748636607275407808710975002453167244211388132280869166 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep204.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (20066309154940202382437977043853789027233261813845634108541543434177679150734 : Int)) * (46524761600908446539585234069489430326657083028801261969728184169836849470343 : Int) =
        (1 : Int) + (35608454956677389840515564246191765027449993579181956579691866429877950008771 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (16045425122321928642851222633670103590917318498255667210140514834515367159515 : Int) * ((2 : Int) * (20066309154940202382437977043853789027233261813845634108541543434177679150734 : Int)) =
        (3 : Int) * (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) + (-40964 : Int) * (-40964 : Int) + (-3887720572045577364808068873814766408088806842568824313376139460561148979511 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int) =
        (16045425122321928642851222633670103590917318498255667210140514834515367159515 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) - (16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) + (-4909914567005605323680735194015718234547297881602128860518894501748373380808 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (15814575136589955221349585958799725147342085565011021245672905698170615381466 : Int) =
        (16045425122321928642851222633670103590917318498255667210140514834515367159515 : Int) * ((16810720316566490990751060652421470777556901491962546143899626636772648017141 : Int) - (28814607045722471110364957977252371237120881648332950145347460831244775941807 : Int)) - (20066309154940202382437977043853789027233261813845634108541543434177679150734 : Int) + (3673200171566367783823013057886082782445195845634805798189693455642135722630 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (93144825497273214550815617421950004906334488422776264561738332 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (93144825497273214550815617421950004906334488422776264561738332 : Nat) = 46572412748636607275407808710975002453167244211388132280869166 + 46572412748636607275407808710975002453167244211388132280869166 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double


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
end ShielddSecurity.ConcretePointTraceStep205
