"""Join the checked135-row constructor to the same SDK/native amounts.

Variable/fixed group rows and the balance output column remain separate joins.
"""
import hashlib
from . import generate_transfer_signed_balance_completion as signed
from . import transfer_signed_balance_completion as plans
from .generate_hash_round import _signature_audits


def generate(metadata_bytes,stream,expected_relation):
    return _from_checked(plans.plan(metadata_bytes,stream,expected_relation))


def _from_checked(recipe):
    parent,parent_source=signed._from_checked(recipe)
    name='RuntimeTransferSignedBalanceNative';n,m,copy=recipe['negative'],recipe['magnitude'],recipe['copy']
    source=f'''import ShielddSecurity.{parent}
import ShielddSecurity.TransferSignedBalanceNative
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact checked metadata SHA256 {recipe['metadata_sha256']}.
-- Exact rendered constructor SHA256 {hashlib.sha256(parent_source.encode()).hexdigest()}.
-- Actual135 local rows only. Group row/output transport remains OPEN.
variable {{F J : Type}} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [AddCommGroup J]

theorem constructed_native_result
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (base blindingBase : J) (asset : F)
    (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) (blinding : F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (nativeAmounts : ∀ i, rho ({parent}.amountColumns i) = ((amounts i).val : F))
    (net : NativeBalanceCommitment.Net)
    (sdkSuccess : NativeBalanceCommitment.sdkNet
      (TransferSignedBalanceNative.inputPair amounts) (TransferSignedBalanceNative.outputPair amounts) = some net)
    (value : Group.Point F)
    (nativeSuccess : NativeTransferAdmission.balanceNative codec writer d
      (fun _ => model.coordinates base) (model.coordinates blindingBase)
      asset (TransferSignedBalanceNative.inputPair amounts) (TransferSignedBalanceNative.outputPair amounts)
      blinding = .ok value) :
    Satisfies ({parent}.completeAssignment rho amounts) {parent}.rawRows ∧
    {parent}.completeAssignment rho amounts {n} =
      (if TransferSignedMagnitude.negative amounts then 1 else 0) ∧
    {parent}.completeAssignment rho amounts {m} = (TransferSignedMagnitude.magnitude amounts : F) ∧
    value = model.coordinates
      ((if TransferSignedMagnitude.negative amounts then
          -(TransferSignedMagnitude.magnitude amounts : Int) else
          (TransferSignedMagnitude.magnitude amounts : Int)) • base +
        codec.decode blinding • blindingBase) := by
  exact ⟨{parent}.original_rows_complete rho amounts one linked nativeAmounts,
    {parent}.final_negative rho amounts,{parent}.final_magnitude rho amounts,
    TransferSignedBalanceNative.native_signed_commitment codec writer d imaginary model nonSquare
      imaginarySquare two base blindingBase asset amounts blinding net sdkSuccess value nativeSuccess⟩

#print axioms constructed_native_result
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
