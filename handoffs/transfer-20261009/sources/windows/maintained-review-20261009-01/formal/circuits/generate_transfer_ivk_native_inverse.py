"""Actual singleton-role bridge from SDK input readers to the IVK constructor.

This adds a source/proof candidate, not evidence qualification. It reuses exact
accepted metadata and original-row plans; no additional ordinary scan occurs.
"""
from . import generate_transfer_prefix_hash_completion as hashes
from . import transfer_ivk_reduction_completion as reduction
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    selected, metadata, _ = hashes.select_ivk(ivk_data, ivk_export, parameter_root,
        expected_relation, readonly_lcs)
    accepted = hashes.ivk.inspect_metadata(ivk_data, parameter_root, expected_relation)
    plan = reduction.plan(reduction_data, accepted, reduction_export, expected_relation, readonly_lcs)
    inputs = [accepted['derived'][handle] for handle in accepted['handles'][:3]]
    if inputs != [((1993, 1),), ((1980, 1),), ((1981, 1),)]:
        raise reduction.relation.RelationError('actual native IVK singleton NK/AK role order')
    hashes.actual_ivk_call(selected)
    copy = metadata['constant_copy']
    if copy in (0, 1980, 1981, 1993) or plan['checked']['metadata']['constant_copy'] != copy:
        raise reduction.relation.RelationError('actual native IVK copy-role independence')
    name = 'RuntimeTransferIvkNativeInverseOwned'
    aliases = dict(P='RuntimeTransferIvkInversePrefixJoin', S='ShielddViewingKeySeed',
                   D='RuntimeHashBlock_authorization_ivk_0')
    source = '''import ShielddSecurity.RuntimeTransferIvkInversePrefixJoin
import ShielddSecurity.ShielddViewingKeySeed
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += '''private theorem actual_inputs : D.callInputs = S.hashInputs := by decide
def completeAssignment {F : Type} [Field F] {Q Encoded Native : Type}
    (fq : GroupNativeSdk.FqBytes Q) (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (base : Nat → F) : Nat → F :=
  P.completed codec (S.seed fq backend nk x y base)
'''
    source += f'''theorem original_rows_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    {{Q R Encoded Native : Type}} (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (nk x y : Q) (scalar : R) (base : Nat → F)
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSource.sdkIvk fq arithmetic initial codec (Poseidon.castParameters D.parameters) nk x y) = some scalar) :
    Satisfies (completeAssignment fq backend codec nk x y base) P.originalRows := by
  have seededOne : S.seed fq backend nk x y base 0 = 1 :=
    (S.seed_preserves fq backend nk x y base 0 (by decide)).trans one
  have seededLink : S.seed fq backend nk x y base {copy} = S.seed fq backend nk x y base 0 := by
    rw [S.seed_preserves fq backend nk x y base {copy} (by decide),
      S.seed_preserves fq backend nk x y base 0 (by decide),linked]
  apply P.original_complete codec (S.seed fq backend nk x y base) seededOne four seededLink
  rw [actual_inputs]
  exact S.seeded_hash_legal fq fr arithmetic initial primitives backend codec
    (Poseidon.castParameters D.parameters) nk x y scalar base accepted
set_option pp.all true in
#check @original_rows_complete
#print axioms original_rows_complete
'''
    return name, joins._qualify(source+f'end ShielddSecurity.{name}\n', aliases)
