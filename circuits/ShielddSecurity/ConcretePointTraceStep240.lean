import ShielddSecurity.ConcretePointTraceStep239
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep240
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 51700705985457181390097522750522957774495280420516535524064981145822294665957
def inputY : F := 33461770856347282676179159932752171262267703893191206623843117220405909122119
def doubleX : F := 12110195515223875010617878644220935489967576916303324778555645575712829753267
def doubleY : F := 4496533041516579545666704447717291031842807406983658523241999777265837166808
def doubleSlope : F := 22769551777769635864896506577451633372441600143447161244972213865912539963875
def addX : F := 4301177741527633080429491099331482822438211492936113279017635361498379141321
def addY : F := 21506660964115946440739536739577060615607286387990367006627659911284871509256
def addSlope : F := 47389158264199768098107210668265879091470962022249462873489506512927393760400
def outX : F := 4301177741527633080429491099331482822438211492936113279017635361498379141321
def outY : F := 21506660964115946440739536739577060615607286387990367006627659911284871509256

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) • base) + ((1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep239.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (33461770856347282676179159932752171262267703893191206623843117220405909122119 : Int)) * (47832442215740650770216851672555534666775423050455154279310932823496945441985 : Int) =
        (1 : Int) + (61048212338480687877485148387174125521813792532241400915161052341924957899533 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (22769551777769635864896506577451633372441600143447161244972213865912539963875 : Int) * ((2 : Int) * (33461770856347282676179159932752171262267703893191206623843117220405909122119 : Int)) =
        (3 : Int) * (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) + (-40964 : Int) * (-40964 : Int) + (-123866912267847130817556527215112124778660808476156880363798133057689194025057 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int) =
        (22769551777769635864896506577451633372441600143447161244972213865912539963875 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) - (51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) + (-9887362162431661828522842159615273201463535898724436186232940154574329901524 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (4496533041516579545666704447717291031842807406983658523241999777265837166808 : Int) =
        (22769551777769635864896506577451633372441600143447161244972213865912539963875 : Int) * ((51700705985457181390097522750522957774495280420516535524064981145822294665957 : Int) - (12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int)) - (33461770856347282676179159932752171262267703893191206623843117220405909122119 : Int) + (-17191630254088511903638054737247515208187900614254613569159501531553337698871 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) • base) + ((1600215917209661574690177627813292414478984684050858711270839639255904114 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (25900808656579679976524531545742161027135415969411485136990698052184605833455 : Int) =
        (1 : Int) + (-13618266214329692762387705312244350298675351591108838848265691430964202687137 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (47389158264199768098107210668265879091470962022249462873489506512927393760400 : Int) * ((12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (4496533041516579545666704447717291031842807406983658523241999777265837166808 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-24916526023249535985924256220930439361688380874730547113260765305171948153774 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int) =
        (47389158264199768098107210668265879091470962022249462873489506512927393760400 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-42828165134824960438708098895157758726499209831887450334167383068265994658169 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (21506660964115946440739536739577060615607286387990367006627659911284871509256 : Int) =
        (47389158264199768098107210668265879091470962022249462873489506512927393760400 : Int) * ((12110195515223875010617878644220935489967576916303324778555645575712829753267 : Int) - (4301177741527633080429491099331482822438211492936113279017635361498379141321 : Int)) - (4496533041516579545666704447717291031842807406983658523241999777265837166808 : Int) + (-7057434970422414745514508989496862794280473438811751169496430721938720359872 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3200431834419323149380355255626584828957969368101717422541679278511808229 : Nat) = 1600215917209661574690177627813292414478984684050858711270839639255904114 + 1600215917209661574690177627813292414478984684050858711270839639255904114 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep240
