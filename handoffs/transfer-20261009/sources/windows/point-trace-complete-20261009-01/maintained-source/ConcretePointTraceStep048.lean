import ShielddSecurity.ConcretePointTraceStep047
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep048
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 25153231165935098296941729463853780492694250103819268966501968632169823924349
def inputY : F := 41984835228654144156636091704408006412901450578268278489830927569996550296479
def doubleX : F := 31110844148777296288379192187436509747959557340149341721634625812348210282365
def doubleY : F := 30953961019282837189677709396655809193352995903129762395371904924721604383842
def doubleSlope : F := 13120062980545001929226425147653173406862024392635362872888227720253076765878
def addX : F := 1279391236065245694412774766013593245181292891422121742832157962491225052482
def addY : F := 30603730848310519894531228960730461671625641126484444369896559406189214429621
def addSlope : F := 23849612413739960848897280998743288775527774811494339106603334686392870236758
def outX : F := 1279391236065245694412774766013593245181292891422121742832157962491225052482
def outY : F := 30603730848310519894531228960730461671625641126484444369896559406189214429621

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((254929103377210 : Nat) • base) + ((254929103377210 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep047.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (41984835228654144156636091704408006412901450578268278489830927569996550296479 : Int)) * (5564199204777702634079379087276007367341753696554549639887823518260897122759 : Int) =
        (1 : Int) + (8910387631055232437540975689205615782403551778836414291822714556065207168817 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (13120062980545001929226425147653173406862024392635362872888227720253076765878 : Int) * ((2 : Int) * (41984835228654144156636091704408006412901450578268278489830927569996550296479 : Int)) =
        (3 : Int) * (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) + (-40964 : Int) * (-40964 : Int) + (-15187459859222154085928523480722922016479093566666445212380113293497766994247 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int) =
        (13120062980545001929226425147653173406862024392635362872888227720253076765878 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) - (25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) + (-3282791639093742705340040222245519262779445221651832023120482628427026936053 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (30953961019282837189677709396655809193352995903129762395371904924721604383842 : Int) =
        (13120062980545001929226425147653173406862024392635362872888227720253076765878 : Int) * ((25153231165935098296941729463853780492694250103819268966501968632169823924349 : Int) - (31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int)) - (41984835228654144156636091704408006412901450578268278489830927569996550296479 : Int) + (1490663735229896447457899924826996170701620659068795947730792909648697446913 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((254929103377210 : Nat) • base) + ((254929103377210 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (327214109786327208787252001157574471544795955273215135307654007848006640032 : Int) =
        (1 : Int) + (-53475180545032740424307148379467298601933707408023246619134502546147873729 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (23849612413739960848897280998743288775527774811494339106603334686392870236758 : Int) * ((31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (30953961019282837189677709396655809193352995903129762395371904924721604383842 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-3897638554115584442560550680874985797657196981175323801004931210031257428380 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int) =
        (23849612413739960848897280998743288775527774811494339106603334686392870236758 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-10847611685433271232591552251307249719019182751319467320935459044607678544154 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (30603730848310519894531228960730461671625641126484444369896559406189214429621 : Int) =
        (23849612413739960848897280998743288775527774811494339106603334686392870236758 : Int) * ((31110844148777296288379192187436509747959557340149341721634625812348210282365 : Int) - (1279391236065245694412774766013593245181292891422121742832157962491225052482 : Int)) - (30953961019282837189677709396655809193352995903129762395371904924721604383842 : Int) + (-13568355392767681354702295716097858604417510277278364126051398713627689988027 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (509858206754421 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (509858206754421 : Nat) = 254929103377210 + 254929103377210 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep048
