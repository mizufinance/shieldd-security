import ShielddSecurity.ConcretePointTraceStep096
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep097
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 15611642098156039252064818416207076062796636688516952229883971198268621294812
def inputY : F := 24588131983877049843316893137041728949182892660697546954365693295357765833005
def doubleX : F := 18710190203772008982898067502487914092422262087760465904063501532865684018082
def doubleY : F := 31084971439867558513976765352744866958676771554512893995766967676519713808308
def doubleSlope : F := 27163435576246564784620749585121864949828445893779997517871220122792542041310
def outX : F := 18710190203772008982898067502487914092422262087760465904063501532865684018082
def outY : F := 31084971439867558513976765352744866958676771554512893995766967676519713808308

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((143512326871937752169391284256 : Nat) • base) + ((143512326871937752169391284256 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep096.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (24588131983877049843316893137041728949182892660697546954365693295357765833005 : Int)) * (9877779255130919149414561604767874345637464515158475193787507799854870456004 : Int) =
        (1 : Int) + (9263739347216007514003955007922812665657914422597549230652742967585053878503 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (27163435576246564784620749585121864949828445893779997517871220122792542041310 : Int) * ((2 : Int) * (24588131983877049843316893137041728949182892660697546954365693295357765833005 : Int)) =
        (3 : Int) * (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) + (-40964 : Int) * (-40964 : Int) + (11530772951657423935869723205168383066550672108978403559659816362092855380108 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (18710190203772008982898067502487914092422262087760465904063501532865684018082 : Int) =
        (27163435576246564784620749585121864949828445893779997517871220122792542041310 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) - (15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) + (-14071515538562227378107366358594495240130192087862018742715648492391587578674 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (31084971439867558513976765352744866958676771554512893995766967676519713808308 : Int) =
        (27163435576246564784620749585121864949828445893779997517871220122792542041310 : Int) * ((15611642098156039252064818416207076062796636688516952229883971198268621294812 : Int) - (18710190203772008982898067502487914092422262087760465904063501532865684018082 : Int)) - (24588131983877049843316893137041728949182892660697546954365693295357765833005 : Int) + (1605145552843300595099804224237322828533556848097128888970269977518215268501 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (287024653743875504338782568512 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (287024653743875504338782568512 : Nat) = 143512326871937752169391284256 + 143512326871937752169391284256 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep097
