import ShielddSecurity.ConcretePointTraceStep232
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep233
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 17161984629568680313537620642466397382453008231007114871551079266105585589916
def inputY : F := 3293007701218363759454646524264533698937855837419325108187892371439148683618
def doubleX : F := 42617445527596125748046873461566306451290650223788228493163168561868178572923
def doubleY : F := 10608788041843827183334650955330536421509350814492615804109908556802777047754
def doubleSlope : F := 6931159131442006203332872750251982963414053019293461317833839914726766754370
def addX : F := 18143046994782760015854533110955317951507927011319605942362129618854640247793
def addY : F := 31536867008158413901505252924368009717278825650594881510413103991050827413766
def addSlope : F := 30138925429471302371331180403786285748150734320210152076653824447581779556851
def outX : F := 18143046994782760015854533110955317951507927011319605942362129618854640247793
def outY : F := 31536867008158413901505252924368009717278825650594881510413103991050827413766

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) • base) + ((12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep232.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (3293007701218363759454646524264533698937855837419325108187892371439148683618 : Int)) * (17991205535056608669355336323811504071134583291337498487595750695596597811242 : Int) =
        (1 : Int) + (2259719254547610878845691536002215886070597495055032014888174734547942315047 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (6931159131442006203332872750251982963414053019293461317833839914726766754370 : Int) * ((2 : Int) * (3293007701218363759454646524264533698937855837419325108187892371439148683618 : Int)) =
        (3 : Int) * (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) + (-40964 : Int) * (-40964 : Int) + (-15980517645250140278285309927445381241527711061499074914118134909052394636536 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int) =
        (6931159131442006203332872750251982963414053019293461317833839914726766754370 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) - (17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) + (-916185087879698805657848490578256424815847000893173715612723817058014279001 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (10608788041843827183334650955330536421509350814492615804109908556802777047754 : Int) =
        (6931159131442006203332872750251982963414053019293461317833839914726766754370 : Int) * ((17161984629568680313537620642466397382453008231007114871551079266105585589916 : Int) - (42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int)) - (3293007701218363759454646524264533698937855837419325108187892371439148683618 : Int) + (3364792704597082280566574247036267137404367159833708311164224053357102236074 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) • base) + ((12501686853200481052267012717291346988117067844147333681803434681686750 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (30842865172913681761630741180223646102484379944451228402778374604973278821619 : Int) =
        (1 : Int) + (1727685757441751567002523122457635891805514704226824588848896081090681532343 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (30138925429471302371331180403786285748150734320210152076653824447581779556851 : Int) * ((42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (10608788041843827183334650955330536421509350814492615804109908556802777047754 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (1688254055424953881907448059951739578672444650322305397096612894385800355864 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int) =
        (30138925429471302371331180403786285748150734320210152076653824447581779556851 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-17323155625981137460348574608210432084656361774916122510609463997807305706290 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (31536867008158413901505252924368009717278825650594881510413103991050827413766 : Int) =
        (30138925429471302371331180403786285748150734320210152076653824447581779556851 : Int) * ((42617445527596125748046873461566306451290650223788228493163168561868178572923 : Int) - (18143046994782760015854533110955317951507927011319605942362129618854640247793 : Int)) - (10608788041843827183334650955330536421509350814492615804109908556802777047754 : Int) + (-14067316886541290001078203432895049854415204710934703397440841981333342791470 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (25003373706400962104534025434582693976234135688294667363606869363373501 : Nat) = 12501686853200481052267012717291346988117067844147333681803434681686750 + 12501686853200481052267012717291346988117067844147333681803434681686750 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep233
