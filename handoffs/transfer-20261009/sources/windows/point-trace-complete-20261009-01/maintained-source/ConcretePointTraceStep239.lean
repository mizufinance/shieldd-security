import ShielddSecurity.ConcretePointTraceStep238
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep239
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 47052145210969971302795790239996070489609335243951289405893096745473092469831
def inputY : F := 9947332390387807912193310390222834115829054029959453814488073969674945730262
def doubleX : F := 51700705985457181390097522750522957774495280420516535524064981145822294665957
def doubleY : F := 33461770856347282676179159932752171262267703893191206623843117220405909122119
def doubleSlope : F := 18360866138691368888633473157070775291219950336164277640390075780635944552683
def outX : F := 51700705985457181390097522750522957774495280420516535524064981145822294665957
def outY : F := 33461770856347282676179159932752171262267703893191206623843117220405909122119

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((800107958604830787345088813906646207239492342025429355635419819627952057 : Nat) • base) + ((800107958604830787345088813906646207239492342025429355635419819627952057 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep238.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (9947332390387807912193310390222834115829054029959453814488073969674945730262 : Int)) * (12913550443515866763057409139206940376971911650222485271183845113504133465303 : Int) =
        (1 : Int) + (4899522633032245843983841145987880409039801312563886591453597166160799402867 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (18360866138691368888633473157070775291219950336164277640390075780635944552683 : Int) * ((2 : Int) * (9947332390387807912193310390222834115829054029959453814488073969674945730262 : Int)) =
        (3 : Int) * (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) + (-40964 : Int) * (-40964 : Int) + (-119697245616413034585661384966027885920509350937023296355217326282408206946767 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) =
        (18360866138691368888633473157070775291219950336164277640390075780635944552683 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) - (47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) + (-6429212905039149903306130158678462211576295018678270426074739889550695093326 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (33461770856347282676179159932752171262267703893191206623843117220405909122119 : Int) =
        (18360866138691368888633473157070775291219950336164277640390075780635944552683 : Int) * ((47052145210969971302795790239996070489609335243951289405893096745473092469831 : Int) - (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int)) - (9947332390387807912193310390222834115829054029959453814488073969674945730262 : Int) + (1627732956356167767543269788343648358126581401497175504895152805710129227303 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) = 800107958604830787345088813906646207239492342025429355635419819627952057 + 800107958604830787345088813906646207239492342025429355635419819627952057 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep239
