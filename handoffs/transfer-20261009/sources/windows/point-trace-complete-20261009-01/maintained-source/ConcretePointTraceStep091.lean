import ShielddSecurity.ConcretePointTraceStep090
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep091
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 48473148037231391718888351392282094392020086869745349554027605405564742908252
def inputY : F := 32984785281461483103409986687486196095303763963871799240315008732312122778749
def doubleX : F := 24885708895992253695808114126417780682261312517943361093399679516010780137388
def doubleY : F := 14039596523690323030843628945369947714262407037426158590812355063976273433909
def doubleSlope : F := 44884944374765750970312499004107557495795933949174289172813681149942952318223
def addX : F := 13189248768049415015311464690063593091844652137897891178804722554501747703579
def addY : F := 42343061399669842103949368665569926207927685960764958752636572914557776937678
def addSlope : F := 17885071499932090484883430097535108906387138602254611401673933984819713529557
def outX : F := 13189248768049415015311464690063593091844652137897891178804722554501747703579
def outY : F := 42343061399669842103949368665569926207927685960764958752636572914557776937678

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((2242380107374027377646738816 : Nat) • base) + ((2242380107374027377646738816 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep090.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (32984785281461483103409986687486196095303763963871799240315008732312122778749 : Int)) * (29449705290856767047999272658326555377241088564919146615356860527106178045149 : Int) =
        (1 : Int) + (37050671982758336176298737416536939652335147390506023540631123004901350016977 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (44884944374765750970312499004107557495795933949174289172813681149942952318223 : Int) * ((2 : Int) * (32984785281461483103409986687486196095303763963871799240315008732312122778749 : Int)) =
        (3 : Int) * (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) + (-40964 : Int) * (-40964 : Int) + (-77959941035049755900744196515245980071374218414589928223250012325587912682714 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int) =
        (44884944374765750970312499004107557495795933949174289172813681149942952318223 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) - (48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) + (-38421371337795492797742864650736828040254362248656063590235117572931799985285 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (14039596523690323030843628945369947714262407037426158590812355063976273433909 : Int) =
        (44884944374765750970312499004107557495795933949174289172813681149942952318223 : Int) * ((48473148037231391718888351392282094392020086869745349554027605405564742908252 : Int) - (24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int)) - (32984785281461483103409986687486196095303763963871799240315008732312122778749 : Int) + (-20190773783440399315946049763422643415756988491625180011230707371351292850078 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((2242380107374027377646738816 : Nat) • base) + ((2242380107374027377646738816 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (15267389837194964533111110036952633304677770200959874620693322580054053230369 : Int) =
        (1 : Int) + (-4307612624833891223267916449611514980735217871263788839671663703367992311112 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (17885071499932090484883430097535108906387138602254611401673933984819713529557 : Int) * ((24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (14039596523690323030843628945369947714262407037426158590812355063976273433909 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-5046177546437695420547587134382429131294788784046670832646575638250761532606 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int) =
        (17885071499932090484883430097535108906387138602254611401673933984819713529557 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-6100323137343598541964007781097766195743341776756285729832219950708228493159 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (42343061399669842103949368665569926207927685960764958752636572914557776937678 : Int) =
        (17885071499932090484883430097535108906387138602254611401673933984819713529557 : Int) * ((24885708895992253695808114126417780682261312517943361093399679516010780137388 : Int) - (13189248768049415015311464690063593091844652137897891178804722554501747703579 : Int)) - (14039596523690323030843628945369947714262407037426158590812355063976273433909 : Int) + (-3989482868087918435737384982294982210298963710268628248578285130343093604002 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (4484760214748054755293477633 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (4484760214748054755293477633 : Nat) = 2242380107374027377646738816 + 2242380107374027377646738816 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep091
