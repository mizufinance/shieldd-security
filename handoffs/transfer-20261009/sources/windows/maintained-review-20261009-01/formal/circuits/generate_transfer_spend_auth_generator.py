"""Bind the actual EPK template operand to the owned SPEND_AUTH program."""
from .generate_hash_round import _signature_audits
from .transfer_relation import RelationError

MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
X = 4139425550610461525665941076812662132363359224232624900223172373014329534291
SIGNED_Y = -12800183797959590982006014900428083432179903968516995553912730489458099309265
Y = SIGNED_Y % MODULUS


def generate(base):
    if (not isinstance(base, tuple) or len(base) != 2 or
            any(type(value) is not int for value in base) or base != (X, SIGNED_Y)):
        raise RelationError('actual signed EPK template generator operand required')
    name = 'RuntimeTransferSpendAuthGenerator'
    text = f'''import ShielddSecurity.NativeSpendAuthGenerator
import ShielddSecurity.RuntimeTransferEpk0FixedWindow000
import ShielddSecurity.NativeEncryptionInitializationSquares
namespace ShielddSecurity.{name}
set_option maxHeartbeats 150000
variable {{F : Type}} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

theorem base_literal : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) =
    NativeSpendAuthGenerator.literal := by
  unfold RuntimeTransferEpk0FixedWindow000.base NativeSpendAuthGenerator.literal
  apply congrArg₂ Group.Point.mk
  · rfl
  · have checked := NativeEncryptionInitializationSquares.polynomial_certificate (F := F)
      ({SIGNED_Y} : Int) {Y} (by decide)
    simpa only [Int.cast_ofNat, Int.cast_neg] using checked

variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
  {{fq : GroupNativeSdk.FqBytes Q}} {{fr : GroupNativeSdk.FrBytes R}}
  {{d : F}} {{model : Group.StandardCurveModel J d}}

/-- The signed physical-template operand is derived from a fixed upstream
standard-generator interpretation and the owned constructor/reader programs.
No per-EPK desired output, subgroup or nonidentity premise is supplied. -/
theorem base_meaning
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream) :
    (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) =
      model.coordinates (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) :=
  base_literal.trans (NativeSpendAuthGenerator.generator_coordinates upstream standard).symm

theorem owned_generator_read {{Raw Encoded : Type}}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)
    (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) :
    (ShielddNativeSdkRaw.generator operations primitives upstream).map
      (ShielddNativePoint.pointValue operations) =
        some (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) := by
  rw [NativeSpendAuthGenerator.raw_generator_read upstream standard codec operations primitives]
  exact congrArg some base_literal.symm
'''
    text += _signature_audits('\n'.join('#print axioms '+name for name in
        ['base_literal','base_meaning','owned_generator_read'])+'\n')
    text += f'\nend ShielddSecurity.{name}\n'
    return name, text
