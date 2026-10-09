"""Bounded dual allocation fences for the complete legal asset cone.

Numeric writes allocate above the map floor; native scalar/bit seeds allocate
inside a distinct low interval. No row-by-255-bit Cartesian checker is emitted.
The original hash chunks are reused directly from their exact source modules.
"""
from . import transfer_asset_map_hash_join as joining
from . import transfer_asset_map_legal_completion as legal
from . import generate_note_hash_block_completion as blocks
from . import transfer_relation as relation


def plan(data, extracted, map_data, map_extracted, inverse_data, inverse_extracted,
         accepted_roles, parameter_root):
    joined = joining.plan(data, extracted, map_data, map_extracted, accepted_roles, parameter_root)
    mapped = legal.plan(map_data, map_extracted, inverse_data, inverse_extracted, accepted_roles)
    recipe = mapped['map']['recipe'];copy = mapped['copy']
    floor = min(c for step in recipe['steps'] for c in step['writes'])
    native_columns = set(recipe['seeds'].values()) | {mapped['quotient']}
    lower, upper = min(native_columns), max(native_columns)+1
    if copy in native_columns or upper > floor:
        raise relation.RelationError('asset hash frame distinct native/numeric allocation cursors')
    context = joined['selected'], joined['checked'], dict(metadata={},readonly_lcs=list(accepted_roles['observed'].values()))
    chunks=[];rows=set();writes=set(recipe['owned_writes']) | set(mapped['writes'])
    for begin in range(0,65,5):
        chunk=blocks._chunk_plan(context,begin,min(begin+5,65))
        for a,b in chunk['raw'].values():
            for column,_ in a+b:
                if column in writes or not ((column==copy or column<floor) and (column<lower or upper<=column)):
                    raise relation.RelationError('asset hash frame original row support overlaps later map/inverse writes')
        chunks.append(chunk);rows.update(chunk['raw'])
    if rows != set(joined['selected']['rows']):
        raise relation.RelationError('asset hash frame exact full65 original row partition')
    return dict(join=joined,map=mapped,copy=copy,floor=floor,lower=lower,upper=upper,chunks=chunks)


def generate(data, extracted, map_data, map_extracted, inverse_data, inverse_extracted,
             accepted_roles, parameter_root, *, hash_base='RuntimeTransferActualAssetHash'):
    from .generate_hash_round import _signature_audits
    from .transfer_note_hash_renaming import _module_name
    _module_name(hash_base)
    result=plan(data,extracted,map_data,map_extracted,inverse_data,inverse_extracted,accepted_roles,parameter_root)
    name='RuntimeTransferAssetConeCompletion';joined='RuntimeTransferAssetMapHashJoin'
    native='RuntimeTransferAssetMapNativeCompletion';seeds='RuntimeTransferAssetMapNativeSeeds'
    numeric='RuntimeTransferAssetMapNumericConstruction';inverse='RuntimeTransferAssetGeneratorInverseCompletion'
    hash_complete=hash_base+'Completion';chunks=[hash_base+'CompletionChunk'+str(i) for i in range(13)]
    copy,floor,lower,upper=(result[k] for k in ('copy','floor','lower','upper'))
    root=result['map']['map']['recipe']['seeds']['selectedRoot'];start=result['map']['map']['recipe']['seeds']['bit0']
    source=f'''import ShielddSecurity.{joined}
import ShielddSecurity.CompilerSequenceCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact qualified hash/native map/inverse parent. Dual source allocation fences.
abbrev modulus := {joined}.modulus
def safe (column : Nat) : Prop :=
  (column = {copy} ∨ column < {floor}) ∧ (column < {lower} ∨ {upper} ≤ column)
instance safeDecidable (column : Nat) : Decidable (safe column) := by unfold safe; infer_instance
def checkSupport (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all (fun term => decide (safe term.1)))
'''
    exports=[]
    for i,chunk in enumerate(chunks):
        source+=f'theorem support{i} : checkSupport {chunk}.rawRows = true := by decide\n'
        exports.append('support'+str(i))
    source+=f'''theorem hash_support : ∀ row ∈ {hash_complete}.rawRows, ∀ term ∈ row.a ++ row.b, safe term.1 := by
  intro row member term present
  simp only [{hash_complete}.rawRows,{','.join(chunk+'.priorRows' for chunk in reversed(chunks[1:]))},List.mem_append,or_assoc] at member
  rcases member with '''+' | '.join('case'+str(i) for i in range(13))+'\n'
    for i in range(13):
        source+=f'  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp support{i} row case{i}) term present)\n'
    source+=f'''variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
theorem preserves (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (column : Nat)
    (outsideHash : column ∉ {hash_complete}.ownedWrites)
    (outsideNumeric : column ∉ PoseidonCompletion.writes {numeric}.steps)
    (outsideOther : column ∉ {seeds}.otherWrites) (outsideRoot : column ≠ {root})
    (outsideBits : column < {start} ∨ {start}+255 ≤ column)
    (outsideInverse : column ∉ {inverse}.ownedWrites) :
    {joined}.completeAssignment codec api rho column = rho column := by
  change {inverse}.completeAssignment ({native}.completeAssignment codec api ({joined}.hashAssignment rho)) column = _
  rw [{inverse}.preserves _ column outsideInverse,
    {native}.preserves codec api ({joined}.hashAssignment rho) column outsideNumeric outsideOther outsideRoot outsideBits]
  exact {hash_complete}.preserves rho column outsideHash

theorem later_preserves (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (column : Nat) (covered : safe column) :
    {joined}.completeAssignment codec api rho column = {joined}.hashAssignment rho column := by
  have numericOutside : column ∉ PoseidonCompletion.writes {numeric}.steps :=
    CompilerSequenceCompletion.frame_column {copy} {floor} [] (PoseidonCompletion.writes {numeric}.steps)
      column {numeric}.writes_checked ⟨covered.1,by simp⟩
  have othersOutside : column ∉ {seeds}.otherWrites := by
    simp only [{seeds}.otherWrites,List.mem_cons,List.not_mem_nil,or_false]
    rcases covered.2 with below | above <;> omega
  have rootOutside : column ≠ {root} := by rcases covered.2 with below | above <;> omega
  have bitsOutside : column < {start} ∨ {start}+255 ≤ column := by
    rcases covered.2 with below | above <;> omega
  have inverseOutside : column ∉ {inverse}.ownedWrites := by
    simp only [{inverse}.ownedWrites,List.mem_cons,List.not_mem_nil,or_false]
    rcases covered.1 with fixed | earlier <;> rcases covered.2 with below | above <;> omega
  change {inverse}.completeAssignment ({native}.completeAssignment codec api ({joined}.hashAssignment rho)) column = _
  rw [{inverse}.preserves _ column inverseOutside]
  exact {native}.preserves codec api ({joined}.hashAssignment rho) column numericOutside othersOutside rootOutside bitsOutside

theorem hash_rows_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    Satisfies ({joined}.completeAssignment codec api rho) {hash_complete}.rawRows := by
  have completed := {hash_complete}.complete_rows rho linked
  intro row member
  have left : eval ({joined}.completeAssignment codec api rho) row.a = eval ({joined}.hashAssignment rho) row.a := by
    apply eval_agrees
    intro term present
    exact later_preserves codec api rho term.1 (hash_support row member term (List.mem_append_left _ present))
  have right : eval ({joined}.completeAssignment codec api rho) row.b = eval ({joined}.hashAssignment rho) row.b := by
    apply eval_agrees
    intro term present
    exact later_preserves codec api rho term.1 (hash_support row member term (List.mem_append_right _ present))
  rw [left,right]
  exact completed row member

def rawRows : List Row := {hash_complete}.rawRows ++ ({native}.rawRows ++ {inverse}.rawRows)
theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec api) blindingGenerator (eval rho {joined}.asset)
      inputs outputs blinding = .ok balance) :
    Satisfies ({joined}.completeAssignment codec api rho) rawRows := by
  have mapped := {joined}.complete_map_inverse cardinality model fullOrder codec writer api rho one four linked
    blindingGenerator inputs outputs blinding balance accepted
  intro row member
  rcases List.mem_append.mp member with hashRow | mapRow
  · exact hash_rows_complete codec api rho linked row hashRow
  · exact mapped row mapRow
'''
    exports+=['hash_support','preserves','later_preserves','hash_rows_complete','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
