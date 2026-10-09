"""Actual NK/AK roles joined to the defined native wallet and IVK constructor.

Capture acceptance binds finite source handles to LCs. Native object/source
construction remains a separate globally functional source interpretation;
neither a capture hash nor a successful unrelated transfer supplies that law.
"""
from . import transfer_authorization_roles as roles
from .transfer_balance_rows import source_index
from .transfer_relation import RelationError
from .generate_hash_round import linear,_signature_audits


def generate(data, expected_relation, accepted_rnk, accepted_ivk):
    try:
        return _generate(data,expected_relation,accepted_rnk,accepted_ivk)
    except (KeyError,TypeError,AttributeError,IndexError) as error:
        raise RelationError('wallet/IVK typed accepted capture metadata') from error


def _generate(data, expected_relation, accepted_rnk, accepted_ivk):
    checked=roles.inspect_metadata(data,expected_relation,accepted_ivk.get('handles'),accepted_rnk,accepted_ivk)
    caller=checked['metadata']['caller'];observed=checked['observed']
    values=([observed[source_index(caller['nk']['source'])]]+
        [observed[source_index(value['source'])] for value in caller['ak']])
    if values != [((1993,1),),((1980,1),),((1981,1),)]:
        raise RelationError('wallet/IVK exact current captured input LCs')
    if checked['metadata']['constant_copy'] != 200692:
        raise RelationError('wallet/IVK exact constant copy')
    name='RuntimeTransferWalletIvkPrefix'
    source='''import ShielddSecurity.RuntimeTransferIvkKeyPrefixOwned
import ShielddSecurity.RuntimeTransferIvkNativeConsumerOwned
import ShielddSecurity.ShielddNativeWalletAssociation
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferWalletIvkPrefix
'''
    source+='-- Actual roles metadata SHA256: '+checked['metadata_sha256']+'\n'
    source+='-- SourceWitness handles are retained separately from compiled LCs.\n'
    for key,value in zip(('nk','akX','akY'),values):
        source+='def '+key+' : Linear := '+linear(value)+'\n'
    source+='''theorem captured_inputs : RuntimeHashBlock_authorization_ivk_0.callInputs = [nk,akX,akY] := by decide

variable {F : Type} [Field F] {E S R K Q Signing J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (d : F) (model : Group.StandardCurveModel J d)
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (guards : ShielddViewingKeyAdmission.Primitives fq fr) (primitives : ShielddNativeWalletAssociation.Primitives)
variable {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (key : K) (walletNk : Q)
variable (wallet : ShielddNativeWalletAssociation.Wallet (S := S) (R := R) (K := K) (Q := Q))
variable (base : Nat → F)
variable (constructed : ShielddNativeWalletAssociation.fromComponents upstream arithmetic initial square codec
  (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) guards primitives key walletNk = some wallet)

def completed : Nat → F := RuntimeTransferIvkKeyPrefixOwned.completeAssignment fq fr d model upstream backend codec
  wallet.nk wallet.authorizationPoint base

include arithmetic initial square guards primitives constructed in
private theorem accepted_wallet : ShielddViewingKeyAdmission.incomingScalar guards
    (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
      (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) wallet.nk
      (upstream.affine (upstream.promote wallet.authorizationPoint)).1
      (upstream.affine (upstream.promote wallet.authorizationPoint)).2) = some wallet.scalar := by
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial square codec
    (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) guards primitives
    key walletNk wallet constructed
  simpa only [fields.2.1,ShielddNativeWalletAssociation.incomingHash,ShielddNativeSdk.coordinateX,ShielddNativeSdk.coordinateY]
    using fields.2.2.2.2.1

include arithmetic initial square guards primitives constructed in
theorem wallet_columns :
    eval (completed fq fr d model upstream backend codec wallet base) nk =
      ShielddNativeIvkHash.fqValue (F := F) fq walletNk ∧
    (⟨eval (completed fq fr d model upstream backend codec wallet base) akX,
      eval (completed fq fr d model upstream backend codec wallet base) akY⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.keyPoint key)) := by
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial square codec
    (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) guards primitives
    key walletNk wallet constructed
  have same := RuntimeTransferIvkKeyPrefixOwned.inputs_preserved fq fr d model upstream backend codec wallet.nk wallet.authorizationPoint base
  rw [captured_inputs] at same
  have first := congrArg (fun values : List F => values[0]?.getD 0) same
  have nativeNk : eval (completed fq fr d model upstream backend codec wallet base) nk =
      ShielddNativeIvkHash.fqValue (F := F) fq wallet.nk := by
    simpa [completed,ShielddViewingKeyCoordinates.seed,ShielddViewingKeySeed.seed,
      ShielddViewingKeySeed.columns,ShielddViewingKeySeed.values,patchAssignment,nk,akX,akY,
      eval,ShielddViewingKeySeed.read_value] using first
  have point := RuntimeTransferIvkKeyPrefixOwned.key_coordinates fq fr d model upstream backend codec wallet.nk wallet.authorizationPoint base key fields.2.2.1
  exact ⟨by simpa only [fields.2.1] using nativeNk,
    by simpa only [completed,akX,akY,eval,Int.cast_one,one_mul,add_zero] using point⟩

include arithmetic initial square guards primitives constructed in
theorem original_rows_complete [CharP F Scalar.modulus]
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base 200692 = base 0) :
    Satisfies (completed fq fr d model upstream backend codec wallet base)
      RuntimeTransferIvkInversePrefixJoin.originalRows :=
  RuntimeTransferIvkKeyPrefixOwned.original_rows_complete fq fr d model upstream backend codec wallet.nk wallet.authorizationPoint base
    arithmetic initial square guards wallet.scalar one four linked
    (accepted_wallet fq fr d model upstream arithmetic initial square guards primitives codec key walletNk wallet constructed)

include arithmetic initial square guards primitives constructed in
theorem wallet_scalar_value [CharP F Scalar.modulus]
    (one : base 0 = 1) (linked : base 200692 = base 0) :
    eval (completed fq fr d model upstream backend codec wallet base)
      RuntimeTransferIvkInverseOwnedCompletion.denominator = (fr.integer wallet.scalar : F) :=
  RuntimeTransferIvkNativeConsumerOwned.native_consumer_value fq fr arithmetic initial square guards backend codec wallet.nk
    (upstream.affine (upstream.promote wallet.authorizationPoint)).1
    (upstream.affine (upstream.promote wallet.authorizationPoint)).2 wallet.scalar base one linked
    (accepted_wallet fq fr d model upstream arithmetic initial square guards primitives codec key walletNk wallet constructed)

include arithmetic initial square guards primitives constructed in
theorem wallet_scalar_integer [CharP F Scalar.modulus]
    (one : base 0 = 1) (linked : base 200692 = base 0) :
    codec.decode (eval (completed fq fr d model upstream backend codec wallet base)
      RuntimeTransferIvkInverseOwnedCompletion.denominator) = fr.integer wallet.scalar :=
  RuntimeTransferIvkNativeConsumerOwned.native_consumer_integer fq fr arithmetic initial square guards backend codec wallet.nk
    (upstream.affine (upstream.promote wallet.authorizationPoint)).1
    (upstream.affine (upstream.promote wallet.authorizationPoint)).2 wallet.scalar base one linked
    (accepted_wallet fq fr d model upstream arithmetic initial square guards primitives codec key walletNk wallet constructed)

include arithmetic initial square guards primitives constructed in
theorem wallet_scalar_reader [CharP F Scalar.modulus]
    (one : base 0 = 1) (linked : base 200692 = base 0) :
    GroupNativeSdk.readScalar fq fr (ShielddScalarReader.decoder backend) wallet.scalar =
      some (eval (completed fq fr d model upstream backend codec wallet base)
        RuntimeTransferIvkInverseOwnedCompletion.denominator) :=
  RuntimeTransferIvkNativeConsumerOwned.native_reader_consumer fq fr arithmetic initial square guards backend codec wallet.nk
    (upstream.affine (upstream.promote wallet.authorizationPoint)).1
    (upstream.affine (upstream.promote wallet.authorizationPoint)).2 wallet.scalar base one linked
    (accepted_wallet fq fr d model upstream arithmetic initial square guards primitives codec key walletNk wallet constructed)
'''
    for export in ('captured_inputs','wallet_columns','original_rows_complete','wallet_scalar_value',
                   'wallet_scalar_integer','wallet_scalar_reader'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
