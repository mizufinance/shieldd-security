"""Required native result join after genuine signed/65/H/final acceptance.

The native Fr reader and independent successful folds supply the primitive
input meaning. The endpoint is derived from the own row constructors. Exact
production asset-function and VALUE_BLINDING object associations remain source
contracts; no endpoint, inverse, nonidentity or row truth is supplied.
This does not change the immutable consumer or runtime recipes.
"""
from . import generate_transfer_balance_group_composition as groups
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(vparent,vpages,bparent,bpages,cparent,cpage,roles,signed,
             asset_base,blinding_base,joint,readonly_lcs=()):
    # Reaccept all genuine parents and the complete original-row/frame plan.
    # The retained one-replay marker alone is never a qualification.
    name,_=groups.generate(vparent,vpages,bparent,bpages,cparent,cpage,roles,signed,
        asset_base,blinding_base,joint,readonly_lcs)
    if name!='RuntimeBalanceGroupComposition':
        raise relation.RelationError('balance native endpoint exact own constructor namespace')
    return _source()


def _source():
    G='RuntimeBalanceGroupComposition'
    D='RuntimeBalanceVariableWindow000Point0Cones'
    A='RuntimeBalanceBlindingFixed'
    S='RuntimeTransferSignedBalanceCompletion'
    F='RuntimeTransferBalanceFinalAddCompletion'
    name='RuntimeBalanceNativeEndpoint'
    source=f'''import ShielddSecurity.{G}
import ShielddSecurity.TransferSignedBalanceNative
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
-- Same actual amounts, native Fr reader, SDK asset point and Binding base.
-- The production asset-function/SDK object association remains a source join;
-- this theorem identifies the own arithmetic endpoint with the independent
-- successful native balance on that SAME object. No new qualification flags.
variable {{E SdkPoint R K Q Signing J Encoded Native Fld : Type}}
variable [Field Fld] [DecidableEq Fld] [CharP Fld Scalar.modulus] [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({D}.coefficientD : Fld))
variable (upstream : ShielddNativeSdk.Upstream E SdkPoint R K Q Signing J fq fr ({D}.coefficientD : Fld) model)
variable (backend : ShielddScalarReader.Backend (F := Fld) Encoded Native)
variable (assetPoint : SdkPoint) (base : Nat → Fld)

theorem native_constructs
    (amounts : TransferSignedMagnitude.Inputs) (nativeBlinding : R)
    (one : base 0 = 1) (linked : base 200692 = base 0)
    (nativeAmounts : ∀ i, base ({S}.amountColumns i) = ((amounts i).val : Fld))
    (blindingReader : ShielddNativeSdk.scalar (fq := fq) (fr := fr) backend nativeBlinding = some (base 2))
    (imaginary : Fld) (nonSquare : Group.NoUnitSquare ({D}.coefficientD : Fld))
    (imaginarySquare : imaginary*imaginary = -1) (four : (4 : Fld) ≠ 0) (two : (2 : Fld) ≠ 0)
    (valueBlinding : J) (valueBlindingRole : ({A}.generator : Group.Point Fld) = model.coordinates valueBlinding)
    (codec : TransferReduction.CanonicalField Fld) (writer : GroupByteCodec.BEWrite codec)
    (net : NativeBalanceCommitment.Net)
    (sdkSuccess : NativeBalanceCommitment.sdkNet (TransferSignedBalanceNative.inputPair amounts)
      (TransferSignedBalanceNative.outputPair amounts) = some net)
    (nativeValue : Group.Point Fld)
    (nativeSuccess : NativeTransferAdmission.balanceNative codec writer ({D}.coefficientD : Fld)
      (fun _ => model.coordinates (upstream.embed (upstream.promote assetPoint)))
      ({A}.generator : Group.Point Fld) (base 6) (TransferSignedBalanceNative.inputPair amounts)
      (TransferSignedBalanceNative.outputPair amounts) (base 2) = .ok nativeValue) :
    Satisfies ({G}.construct fq fr model upstream backend assetPoint base amounts (fr.integer nativeBlinding))
      ({G}.ownedRows (TransferSignedMagnitude.magnitude amounts)) ∧
    {F}.outputPoint ({G}.construct fq fr model upstream backend assetPoint base amounts (fr.integer nativeBlinding)) =
      nativeValue := by
  have reader := ShielddNativeSdk.scalar_read (fq := fq) (fr := fr) backend nativeBlinding
  rw [blindingReader] at reader
  have inputValue : base 2 = (fr.integer nativeBlinding : Fld) := Option.some.inj reader
  have built := {G}.constructs fq fr model upstream backend assetPoint base amounts
    (fr.integer nativeBlinding) (fr.bounded nativeBlinding) one linked inputValue nativeAmounts
    imaginary nonSquare imaginarySquare four valueBlinding valueBlindingRole
  have nativeAcceptance := nativeSuccess
  rw [valueBlindingRole] at nativeAcceptance
  have observed := TransferSignedBalanceNative.native_signed_commitment codec writer
    ({D}.coefficientD : Fld) imaginary model nonSquare imaginarySquare two
    (upstream.embed (upstream.promote assetPoint)) valueBlinding (base 6) amounts (base 2)
    net sdkSuccess nativeValue nativeAcceptance
  have decoded : codec.decode (base 2) = fr.integer nativeBlinding := by
    rw [inputValue]
    exact TransferReduction.decode_canonical_cast codec _
      (lt_trans (fr.bounded nativeBlinding) (by decide : Scalar.order < Scalar.modulus))
  have nativeCoordinates : nativeValue = model.coordinates
      ((if TransferSignedMagnitude.negative amounts then
          -(TransferSignedMagnitude.magnitude amounts • upstream.embed (upstream.promote assetPoint)) else
            TransferSignedMagnitude.magnitude amounts • upstream.embed (upstream.promote assetPoint)) +
        fr.integer nativeBlinding • valueBlinding) := by
    simpa only [decoded,ite_smul,neg_smul,natCast_zsmul] using observed
  exact ⟨built.1,built.2.trans nativeCoordinates.symm⟩
#print axioms native_constructs
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
