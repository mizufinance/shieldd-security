import ShielddSecurity.ConcretePointTraceStep249
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep250
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 2831284930826257191850187232551642402086626139799524735967873635909311110677
def inputY : F := 32716214748985956159375712475996032039789345680637979423244305125903608692678
def doubleX : F := 40532404291600356176169554744058488321345054232357191740446803600390823982019
def doubleY : F := 44002237478645917022677495582480480715717369515719097446475485199168347043958
def doubleSlope : F := 40114998070567449572063496291785656464289690142808742812151937308523680413362
def addX : F := 41334362864534015912584928801566269682090065139862152751704272394126511954464
def addY : F := 42626622320796312627407042081663664036453466781731634990546728550724620397934
def addSlope : F := 35634848074285233741372739577241047946682732676879761700801874310336598615832
def outX : F := 41334362864534015912584928801566269682090065139862152751704272394126511954464
def outY : F := 42626622320796312627407042081663664036453466781731634990546728550724620397934

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) • base) + ((1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep249.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (32716214748985956159375712475996032039789345680637979423244305125903608692678 : Int)) * (35720968013836277430869060421801718655201346964787536461367350647906674783808 : Int) =
        (1 : Int) + (44574629742680309873329216235655882891023933646529334122986841879930658712319 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (40114998070567449572063496291785656464289690142808742812151937308523680413362 : Int) * ((2 : Int) * (32716214748985956159375712475996032039789345680637979423244305125903608692678 : Int)) =
        (3 : Int) * (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) + (-40964 : Int) * (-40964 : Int) + (49599119902147289125748788053817366871474677494739080263972569184170291154797 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int) =
        (40114998070567449572063496291785656464289690142808742812151937308523680413362 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) - (2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) + (-30689162044633643740921107615495323300613038566382693026529798902320907969503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (44002237478645917022677495582480480715717369515719097446475485199168347043958 : Int) =
        (40114998070567449572063496291785656464289690142808742812151937308523680413362 : Int) * ((2831284930826257191850187232551642402086626139799524735967873635909311110677 : Int) - (40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int)) - (32716214748985956159375712475996032039789345680637979423244305125903608692678 : Int) + (28842473313635247301346108457960061777958703452238377424899983261313554349880 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) • base) + ((1638621099222693452482741890880811432426480316468079320341339790598045813549 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (15714826661441513135557508156089074550179969178345952433441715961870503485836 : Int) =
        (1 : Int) + (255398861660371105865659380187969259762676900311816545380561411091747479615 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (35634848074285233741372739577241047946682732676879761700801874310336598615832 : Int) * ((40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (44002237478645917022677495582480480715717369515719097446475485199168347043958 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (579140949479481998360263691005067717149456552054047397398371819744053187380 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int) =
        (35634848074285233741372739577241047946682732676879761700801874310336598615832 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-24217053554200243592216492213845806324484894849600076633246926972099996786002 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42626622320796312627407042081663664036453466781731634990546728550724620397934 : Int) =
        (35634848074285233741372739577241047946682732676879761700801874310336598615832 : Int) * ((40532404291600356176169554744058488321345054232357191740446803600390823982019 : Int) - (41334362864534015912584928801566269682090065139862152751704272394126511954464 : Int)) - (44002237478645917022677495582480480715717369515719097446475485199168347043958 : Int) + (545002287325564500454031422461183960231882746816218495568717243056362187164 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (3277242198445386904965483781761622864852960632936158640682679581196091627099 : Nat) = 1638621099222693452482741890880811432426480316468079320341339790598045813549 + 1638621099222693452482741890880811432426480316468079320341339790598045813549 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep250
