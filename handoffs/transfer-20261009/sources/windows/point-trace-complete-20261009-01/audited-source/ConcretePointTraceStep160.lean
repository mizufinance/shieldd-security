import ShielddSecurity.ConcretePointTraceStep159
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep160
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 6174854229412295567172660711483373808468036944033653047592785988030350830750
def inputY : F := 15755458460230156283510646336334208568769923356930467633590082181634813809287
def doubleX : F := 29257403165280665011829228934008090092146577291637224959362513291873378844071
def doubleY : F := 2039098492782296086996805875910007308843266306630411588843258172745307946280
def doubleSlope : F := 27680789414848145978473202775123266647411485218796621049568813701745046235144
def addX : F := 14921983627863233452171159185278874711105732371475696218170192373884026736564
def addY : F := 19102744592094582575807867208215381237214898910546985844095458571759001678282
def addSlope : F := 34677745746591056322884374267440802963798592858891371064936137206288697947674
def outX : F := 14921983627863233452171159185278874711105732371475696218170192373884026736564
def outY : F := 19102744592094582575807867208215381237214898910546985844095458571759001678282

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((1323667582614592881651782610986600799752956283196 : Nat) • base) + ((1323667582614592881651782610986600799752956283196 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep159.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (15755458460230156283510646336334208568769923356930467633590082181634813809287 : Int)) * (18459548839748786847323078815192686227686787912014258451320153565849705598184 : Int) =
        (1 : Int) + (11093117220525226649821772234009791078692560174827400531613028404321013447855 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (27680789414848145978473202775123266647411485218796621049568813701745046235144 : Int) * ((2 : Int) * (15755458460230156283510646336334208568769923356930467633590082181634813809287 : Int)) =
        (3 : Int) * (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) + (-40964 : Int) * (-40964 : Int) + (14453093015982841776920943783818325110019754575612664545560362467530055159220 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int) =
        (27680789414848145978473202775123266647411485218796621049568813701745046235144 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) - (6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) + (-14612631143660990472094341143528562959193761306975863492256665719874657757541 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (2039098492782296086996805875910007308843266306630411588843258172745307946280 : Int) =
        (27680789414848145978473202775123266647411485218796621049568813701745046235144 : Int) * ((6174854229412295567172660711483373808468036944033653047592785988030350830750 : Int) - (29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int)) - (15755458460230156283510646336334208568769923356930467633590082181634813809287 : Int) + (12185229561206839090646469495030871039700032794435671768161794356151540924407 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((1323667582614592881651782610986600799752956283196 : Nat) • base) + ((1323667582614592881651782610986600799752956283196 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (19744569391890841880241454957091559810680607555318556591221435648481036413132 : Int) =
        (1 : Int) + (-3924676773218807349409665603055737473996882110439637725811506324483455574545 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (34677745746591056322884374267440802963798592858891371064936137206288697947674 : Int) * ((29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (2039098492782296086996805875910007308843266306630411588843258172745307946280 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-6892981081427356010917699082963525156920608019258930152146970744321204367094 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int) =
        (34677745746591056322884374267440802963798592858891371064936137206288697947674 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-22933650788681054752719470700546031498791082163634815686015465213440085706302 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (19102744592094582575807867208215381237214898910546985844095458571759001678282 : Int) =
        (34677745746591056322884374267440802963798592858891371064936137206288697947674 : Int) * ((29257403165280665011829228934008090092146577291637224959362513291873378844071 : Int) - (14921983627863233452171159185278874711105732371475696218170192373884026736564 : Int)) - (2039098492782296086996805875910007308843266306630411588843258172745307946280 : Int) + (-9480532788458017998075188921276902126049321035571727235660280632661680750012 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (2647335165229185763303565221973201599505912566393 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (2647335165229185763303565221973201599505912566393 : Nat) = 1323667582614592881651782610986600799752956283196 + 1323667582614592881651782610986600799752956283196 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add


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
end ShielddSecurity.ConcretePointTraceStep160
