"""Construct every actual selected map row from native roots and owned writes.

The rawRows conclusion is a symbolic union of already exact original row
modules. Its numeric/canonical overlap is intentional; the distinct original
physical row partition is checked before generation. Source/native ABI
correspondence and the separate generator admission inverse remain joins.
"""
from . import transfer_asset_map_completion as completion,transfer_asset_map_canonical_sequence as sequence
from . import transfer_asset_map_seed_assertions as assertions,transfer_asset_map_native_first_rows as first
from . import transfer_asset_map_native_root_rows as roots,transfer_asset_map_native_rational_rows as rational
from . import transfer_asset_map_native_double_rows as doubles,transfer_relation as relation


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles)
    seq=sequence.plan(data,extracted,accepted_roles)
    groups=[seq['original_indices'],assertions.plan(data,extracted,accepted_roles)['indices'],
            [first.plan(data,extracted,accepted_roles)['assertion']],roots.plan(data,extracted,accepted_roles)['indices'],
            rational.plan(data,extracted,accepted_roles)['indices']]
    groups.extend([doubles.plan(data,extracted,accepted_roles,i)['assertion']] for i in range(3))
    indices=[i for group in groups for i in group]
    if len(indices)!=len(set(indices)) or set(indices)!=set(recipe['raw']):
        raise relation.RelationError('native completion exact full original row partition')
    if len(seq['original_indices'])!=858 or len(indices)!=870:
        raise relation.RelationError('native completion bounded actual map870 partition')
    return dict(recipe=recipe,sequence=seq,groups=groups,indices=sorted(indices))


def generate(data,extracted,accepted_roles):
    return _from_checked(plan(data,extracted,accepted_roles))


def _from_checked(result):
    from .generate_hash_round import _signature_audits
    recipe=result['recipe'];copy=recipe['checked']['metadata']['constant_copy']
    native='RuntimeTransferAssetMapNativeSeeds';seq='RuntimeTransferAssetMapCanonicalSequence'
    modules=[seq,'RuntimeTransferAssetMapSeedAssertions','RuntimeTransferAssetMapNativeFirstRows',
             'RuntimeTransferAssetMapNativeRootRows','RuntimeTransferAssetMapNativeRationalRows']
    modules.extend('RuntimeTransferAssetMapNativeDouble'+str(i) for i in range(3))
    name='RuntimeTransferAssetMapNativeCompletion';numeric='RuntimeTransferAssetMapNumericConstruction'
    root=recipe['seeds']['selectedRoot'];start=recipe['seeds']['bit0']
    source=''.join('import ShielddSecurity.'+module+'\n' for module in modules)+f'''set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- The union repeats508 identical numeric/canonical rows. Every distinct
-- selected physical row is owned by exactly one group in the checked plan.
abbrev modulus := {native}.modulus
def distinctOriginalRowIndices : List Nat := {result['indices']}
def rawChunks : List (List Row) := [{','.join(module+'.rawRows' for module in modules)}]
def rawRows : List Row := rawChunks.flatten
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev completeAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho

theorem canonical_complete (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec api rho) {seq}.rawRows := by
  have seedOne : {native}.seedOther codec api rho 0 = 1 := by
    unfold {native}.seedOther
    rw [patchAssignment_preserves rho _ {native}.otherWrites 0 (by decide)]
    exact one
  have seedLinked : {native}.seedOther codec api rho {copy} = {native}.seedOther codec api rho 0 := by
    unfold {native}.seedOther
    rw [patchAssignment_preserves rho _ {native}.otherWrites {copy} (by decide),
      patchAssignment_preserves rho _ {native}.otherWrites 0 (by decide),linked]
  change Satisfies ({numeric}.completeAssignment
    (RuntimeTransferAssetMapNativeBits.completeAssignment codec ({native}.seedOther codec api rho)
      ({native}.nativeY codec api rho))) {seq}.rawRows
  rw [← {seq}.assignment_equal codec ({native}.seedOther codec api rho) ({native}.nativeY codec api rho)]
  exact {seq}.complete_rows codec ({native}.seedOther codec api rho) ({native}.nativeY codec api rho)
    seedOne four seedLinked

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec api rho) rawRows := by
  intro row member
  obtain ⟨chunk,present,inChunk⟩ := List.mem_flatten.mp member
  simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with '''+' | '.join('case'+str(i) for i in range(len(modules)))+'\n'
    for i,module in enumerate(modules):
        if i==0:call='canonical_complete codec api rho one four linked'
        elif i==1:call=module+'.complete_rows cardinality codec api rho linked'
        elif i==4:call=module+'.complete_rows codec api rho one four linked'
        else:call=module+'.complete_rows cardinality codec api rho one four linked'
        source+=f'  · subst chunk; exact {call} row inChunk\n'
    source+=f'''
theorem preserves (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (column : Nat)
    (outsideNumeric : column ∉ PoseidonCompletion.writes {numeric}.steps)
    (outsideOther : column ∉ {native}.otherWrites) (outsideRoot : column ≠ {root})
    (outsideBits : column < {start} ∨ {start}+255 ≤ column) :
    completeAssignment codec api rho column = rho column := by
  unfold completeAssignment {native}.completeAssignment
  rw [{numeric}.preserves _ column outsideNumeric]
  exact {native}.preserves codec api rho column outsideOther outsideRoot outsideBits

theorem native_cofactor [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    RuntimeTransferAssetMapNativeDouble2.output (completeAssignment codec api rho) =
      {native}.nativePoint3 codec api rho :=
  RuntimeTransferAssetMapNativeDouble2.output_native cardinality codec api rho one four linked
'''
    exports=['canonical_complete','complete_rows','preserves','native_cofactor']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
