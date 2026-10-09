"""Bind the actual domain26 hash constructor to the lawful map/inverse lane.

The source joins exact asset/input/output LCs, actual parameters, and retained
typed source handles. It completes the map and inverse on the hash assignment;
preserving the hash rows through later writes remains a separate frame proof.
"""
from . import transfer_asset_hash as hashes, transfer_asset_map_completion as maps
from . import transfer_relation as relation


def plan(data, extracted, map_data, map_extracted, accepted_roles, parameter_root):
    checked = hashes.inspect_metadata(data, map_data, accepted_roles, parameter_root)
    selected = hashes.round_selection(data, extracted, map_data, accepted_roles, parameter_root)
    mapped = maps.plan(map_data, map_extracted, accepted_roles)
    observed = checked['observed']
    def terms(ref):
        return observed[tuple(ref['source'])]
    asset = terms(checked['metadata']['hash']['inputs'][0])
    output = terms(checked['metadata']['hash']['output'])
    if output != mapped['checked']['values']['u']:
        raise relation.RelationError('asset hash exact map native input LC join')
    return dict(checked=checked, selected=selected, mapped=mapped, asset=asset, output=output)


def generate(data, extracted, map_data, map_extracted, accepted_roles, parameter_root,
             *, hash_base='RuntimeTransferActualAssetHash'):
    from .generate_hash_round import linear, _signature_audits
    from .transfer_note_hash_renaming import _module_name
    _module_name(hash_base)
    result = plan(data, extracted, map_data, map_extracted, accepted_roles, parameter_root)
    checked = result['checked'];copy = checked['metadata']['constant_copy']
    core = 'RuntimeTransferAssetMapFirstCubicConstruction'
    legal = 'RuntimeTransferAssetMapLegalCompletion'
    native = 'RuntimeTransferAssetMapNativeCompletion'
    inverse = 'RuntimeTransferAssetGeneratorInverseCompletion'
    constructor = hash_base + 'Completion'
    parameters = 'RuntimeHashBlock_balance0_asset0_permutation0_0.parameters'
    name = 'RuntimeTransferAssetMapHashJoin'
    source = f'''import ShielddSecurity.{constructor}
import ShielddSecurity.{legal}
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact domain26/one input/full65 rounds, metadata {checked['metadata_sha256']}.
-- This closes asset->hash->u for map/inverse construction. Hash row framing
-- through the later map/inverse writes is a separate explicit obligation.
abbrev modulus := {legal}.modulus
def asset : Linear := {linear(result['asset'])}
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev hashAssignment (rho : Nat → F) := {constructor}.completeAssignment rho
def nativeAssetGenerator (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (value : F) : Group.Point F :=
  {legal}.nativeGenerator codec api
    (Poseidon.hash3 (Poseidon.castParameters {parameters}) 26 [value])
def completeAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : Nat → F :=
  {legal}.completeAssignment codec api (hashAssignment rho)

theorem inputs_exact : {hash_base}.inputs = [asset] := rfl
theorem output_exact : {core}.input = {hash_base}.output := rfl
theorem map_input_value (rho : Nat → F) (one : rho 0 = 1) (linked : rho {copy} = rho 0) :
    {core}.nativeInput (hashAssignment rho) =
      Poseidon.hash3 (Poseidon.castParameters {parameters}) 26 [eval rho asset] := by
  have value := ({constructor}.complete_hash rho one linked).2.1
  change eval (hashAssignment rho) {core}.input = _
  rw [output_exact]
  simpa only [inputs_exact,List.map_cons,List.map_nil] using value
theorem hash_one (rho : Nat → F) (one : rho 0 = 1) : hashAssignment rho 0 = 1 :=
  ({constructor}.preserves rho 0 (by decide)).trans one
theorem hash_linked (rho : Nat → F) (linked : rho {copy} = rho 0) :
    hashAssignment rho {copy} = hashAssignment rho 0 := by
  change {constructor}.completeAssignment rho {copy} = {constructor}.completeAssignment rho 0
  rw [{constructor}.preserves rho {copy} (by decide),{constructor}.preserves rho 0 (by decide),linked]

theorem complete_map_inverse [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      (nativeAssetGenerator codec api) blindingGenerator (eval rho asset)
      inputs outputs blinding = .ok balance) :
    Satisfies (completeAssignment codec api rho) ({native}.rawRows ++ {inverse}.rawRows) := by
  have mapped : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({legal}.nativeGenerator codec api) blindingGenerator ({core}.nativeInput (hashAssignment rho))
      inputs outputs blinding = .ok balance := by
    rw [map_input_value rho one linked]
    simpa only [NativeTransferAdmission.balanceNative,nativeAssetGenerator] using accepted
  exact {legal}.complete_rows cardinality model fullOrder codec writer api (hashAssignment rho)
    (hash_one rho one) four (hash_linked rho linked) blindingGenerator inputs outputs blinding balance mapped
'''
    exports = ['inputs_exact', 'output_exact', 'map_input_value', 'hash_one', 'hash_linked', 'complete_map_inverse']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
