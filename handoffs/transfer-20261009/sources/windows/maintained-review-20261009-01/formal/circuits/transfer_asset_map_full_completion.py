"""Complete earlier asset-ID inverse rows and the captured hash/map cone.

The two native admission boundaries are independent: registry proof retrieval
excludes asset ID zero; successful native balance excludes a mapped identity.
The actual eight support columns are preserved through all later writes.
"""
from . import transfer_asset_map_hash_frame as frame
from . import transfer_asset_nonzero as nonzero, transfer_relation as relation

EARLIER_COLUMNS = (0, 1, 2, 6, 1992, 49790, 49791, 200692)


def _check_later(result):
    if result['join']['asset'] != ((6, 1),) or result['copy'] != 200692:
        raise relation.RelationError('whole asset cone exact earlier asset/copy LC join')
    columns = set(EARLIER_COLUMNS)
    recipe = result['map']['map']['recipe']
    later = set(recipe['owned_writes']) | set(result['map']['writes'])
    for chunk in result['chunks']:
        later.update(chunk['writes'])
    if columns & later:
        raise relation.RelationError('whole asset cone later write overlaps earlier rows/shared roles')
    if any(not ((column == result['copy'] or column < result['floor']) and
                (column < result['lower'] or result['upper'] <= column)) for column in columns):
        raise relation.RelationError('whole asset cone exact earlier dual cursor support')


def plan(data, extracted, map_data, map_extracted, inverse_data, inverse_extracted,
         earlier_extracted, accepted_roles, parameter_root):
    nonzero._validate(earlier_extracted)
    result = frame.plan(data, extracted, map_data, map_extracted, inverse_data,
                        inverse_extracted, accepted_roles, parameter_root)
    if any(item['identity'] != earlier_extracted['identity'] for item in
           (extracted, map_extracted, inverse_extracted)):
        raise relation.RelationError('whole asset cone exact earlier full ordinary identity')
    _check_later(result)
    return result


def generate(data, extracted, map_data, map_extracted, inverse_data, inverse_extracted,
             earlier_extracted, accepted_roles, parameter_root, *, hash_base='RuntimeTransferActualAssetHash'):
    from .generate_hash_round import _signature_audits
    from .transfer_note_hash_renaming import _module_name
    _module_name(hash_base)
    result = plan(data, extracted, map_data, map_extracted, inverse_data, inverse_extracted,
                  earlier_extracted, accepted_roles, parameter_root)
    name='RuntimeTransferCompleteAssetCone';early='RuntimeTransferAssetNonzero'
    joined='RuntimeTransferAssetMapHashJoin';whole='RuntimeTransferAssetConeCompletion'
    hash_complete=hash_base+'Completion';native='RuntimeTransferAssetMapNativeSeeds'
    numeric='RuntimeTransferAssetMapNumericConstruction';inverse='RuntimeTransferAssetGeneratorInverseCompletion'
    root=result['map']['map']['recipe']['seeds']['selectedRoot']
    start=result['map']['map']['recipe']['seeds']['bit0']
    source=f'''import ShielddSecurity.{whole}
import ShielddSecurity.{early}
import ShielddSecurity.NativeAssetAdmission
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Same independently replayed full ordinary relation; no earlier write is
-- overwritten by the actual later hash/native/inverse programs.
abbrev modulus := {joined}.modulus
def earlierColumns : List Nat := {list(EARLIER_COLUMNS)}
theorem asset_exact : {joined}.asset = [(6,1)] := rfl
theorem earlier_support_checked : {early}.rawRows.all (fun row =>
    (row.a ++ row.b).all (fun term => decide (term.1 ∈ earlierColumns))) = true := by decide
theorem map_fence_checked : earlierColumns.all (fun column => decide ({whole}.safe column)) = true := by decide
'''
    exports=['asset_exact','earlier_support_checked','map_fence_checked']
    for i in range(13):
        source+=f'''theorem hash_writes_checked{i} : {hash_base}CompletionChunk{i}.ownedWrites.all
    (fun written => earlierColumns.all (fun column => decide (column ≠ written))) = true := by decide
'''
        exports.append('hash_writes_checked'+str(i))
    source+=f'''theorem hash_outside (column : Nat) (kept : column ∈ earlierColumns) :
    column ∉ {hash_complete}.ownedWrites := by
  have finite : ∀ i : Fin 13, column ∉ {hash_complete}.chunkWrites i.val := by
    '''
    for i in range(13):
        indent='    '+'  '*i
        source+='refine Fin.cases ?_ ?_\n'+indent+'· intro present\n'
        source+=indent+f'  change column ∈ {hash_base}CompletionChunk{i}.ownedWrites at present\n'
        source+=indent+f'  have different := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hash_writes_checked{i} column present) column kept)\n'
        source+=indent+'  exact different rfl\n'+indent+'· '
    source+=f'''intro impossible; exact Fin.elim0 impossible
  intro written
  obtain ⟨index,bounded,present⟩ := List.mem_flatMap.mp written
  exact finite ⟨index,List.mem_range.mp bounded⟩ present

variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev initialAssignment (rho : Nat → F) := {early}.completeAssignment rho
def completeAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : Nat → F :=
  {joined}.completeAssignment codec api (initialAssignment rho)
def rawRows : List Row := {early}.rawRows ++ {whole}.rawRows

theorem preserves_earlier (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (column : Nat)
    (kept : column ∈ earlierColumns) : completeAssignment codec api rho column = initialAssignment rho column := by
  have covered := of_decide_eq_true (List.all_eq_true.mp map_fence_checked column kept)
  change {joined}.completeAssignment codec api (initialAssignment rho) column = _
  rw [{whole}.later_preserves codec api (initialAssignment rho) column covered]
  exact {hash_complete}.preserves (initialAssignment rho) column (hash_outside column kept)

theorem earlier_complete {{Proof : Type}} (fetch : F → Except NativeAssetAdmission.Error Proof)
    (proof : Proof) (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (one : rho 0 = 1)
    (admitted : NativeAssetAdmission.proofDataNative fetch (rho 6) = .ok proof) :
    Satisfies (completeAssignment codec api rho) {early}.rawRows := by
  have constructed := {early}.complete_satisfies rho one
    (NativeAssetAdmission.proof_data_success_nonzero fetch (rho 6) proof admitted)
  intro row member
  have agrees : ∀ term ∈ row.a ++ row.b,
      completeAssignment codec api rho term.1 = initialAssignment rho term.1 := by
    intro term present
    exact preserves_earlier codec api rho term.1
      (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp earlier_support_checked row member) term present))
  have left : eval (completeAssignment codec api rho) row.a = eval (initialAssignment rho) row.a := by
    apply eval_agrees
    intro term present
    exact agrees term (List.mem_append_left _ present)
  have right : eval (completeAssignment codec api rho) row.b = eval (initialAssignment rho) row.b := by
    apply eval_agrees
    intro term present
    exact agrees term (List.mem_append_right _ present)
  rw [left,right]
  exact constructed row member

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    {{Proof : Type}} (fetch : F → Except NativeAssetAdmission.Error Proof) (proof : Proof)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (admitted : NativeAssetAdmission.proofDataNative fetch (rho 6) = .ok proof)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec api) blindingGenerator (eval rho {joined}.asset)
      inputs outputs blinding = .ok balance) :
    Satisfies (completeAssignment codec api rho) rawRows := by
  have initialOne : initialAssignment rho 0 = 1 := ({early}.complete_preserves_roles rho).1.trans one
  have initialCopy : initialAssignment rho 200692 = 1 := by simp [initialAssignment,{early}.completeAssignment]
  have initialAsset : eval (initialAssignment rho) {joined}.asset = eval rho {joined}.asset := by
    rw [asset_exact]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact ({early}.complete_preserves_roles rho).2.2.2
  have balanceAccepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec api) blindingGenerator (eval (initialAssignment rho) {joined}.asset)
      inputs outputs blinding = .ok balance := by rw [initialAsset]; exact accepted
  have later := {whole}.complete_rows cardinality model fullOrder codec writer api (initialAssignment rho)
    initialOne four (initialCopy.trans initialOne.symm) blindingGenerator inputs outputs blinding balance balanceAccepted
  intro row member
  rcases List.mem_append.mp member with earlyRow | laterRow
  · exact earlier_complete fetch proof codec api rho one admitted row earlyRow
  · exact later row laterRow

theorem shared_roles (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    completeAssignment codec api rho 0 = rho 0 ∧ completeAssignment codec api rho 1 = rho 1 ∧
      completeAssignment codec api rho 2 = rho 2 ∧ completeAssignment codec api rho 6 = rho 6 := by
  have kept := {early}.complete_preserves_roles rho
  exact ⟨(preserves_earlier codec api rho 0 (by decide)).trans kept.1,
    (preserves_earlier codec api rho 1 (by decide)).trans kept.2.1,
    (preserves_earlier codec api rho 2 (by decide)).trans kept.2.2.1,
    (preserves_earlier codec api rho 6 (by decide)).trans kept.2.2.2⟩

theorem preserves (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (column : Nat) (outsideEarlier : column ∉ {early}.completionWrites)
    (outsideHash : column ∉ {hash_complete}.ownedWrites)
    (outsideNumeric : column ∉ PoseidonCompletion.writes {numeric}.steps)
    (outsideOther : column ∉ {native}.otherWrites) (outsideRoot : column ≠ {root})
    (outsideBits : column < {start} ∨ {start}+255 ≤ column)
    (outsideInverse : column ∉ {inverse}.ownedWrites) : completeAssignment codec api rho column = rho column := by
  exact ({whole}.preserves codec api (initialAssignment rho) column outsideHash outsideNumeric
    outsideOther outsideRoot outsideBits outsideInverse).trans ({early}.complete_preserves rho column outsideEarlier)
'''
    exports+=['hash_outside','preserves_earlier','earlier_complete','complete_rows','shared_roles','preserves']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
