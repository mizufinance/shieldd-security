"""Compose actual numeric map constructors with bounded suffix support proofs.

This completes original materialization rows from arbitrary seeded assignments.
The native seed and asserted-square/QR/inverse/parity/endpoint phase remain a
mandatory separate join; no row-satisfaction premise stands in for that phase.
"""
from . import transfer_asset_map_completion as completion, transfer_relation as relation


def plan(data, extracted, accepted_roles):
    recipe = completion.plan(data, extracted, accepted_roles)
    chunks = [recipe['steps'][i:i+8] for i in range(0, len(recipe['steps']), 8)]
    copy = recipe['checked']['metadata']['constant_copy'];parts = []
    for number, chunk in enumerate(chunks):
        indices = sorted({index for step in chunk for index in step['rows']})
        support = {column for index in indices for lc in recipe['raw'][index] for column, _ in lc}
        floor = max(support - {copy}, default=0) + 1
        future = {column for rest in chunks[number+1:] for step in rest for column in step['writes']}
        exceptions = sorted(column for column in future if column < floor)
        if len(exceptions) > 8 or support & future or copy in future:
            raise relation.RelationError('map numeric suffix freshness/exception bound')
        parts.append(dict(number=number, rows=indices, floor=floor, exceptions=exceptions,
                          future_writes=sorted(future)))
    partition = [index for part in parts for index in part['rows']]
    if len(partition) != len(set(partition)) or set(partition) != set(recipe['material_rows']):
        raise relation.RelationError('map numeric sequence exact original-row partition')
    seed_floor = min(column for step in recipe['steps'] for column in step['writes'])
    if any(column >= seed_floor for column in recipe['seeds'].values()):
        raise relation.RelationError('map numeric native seed allocation fence')
    return dict(recipe=recipe, chunks=chunks, parts=parts, original_partition=partition, seed_floor=seed_floor)


def generate_supports(data, extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    result = plan(data, extracted, accepted_roles);parts=result['parts']
    copy=result['recipe']['checked']['metadata']['constant_copy'];modules={}
    for part in parts:
        number=part['number'];name='RuntimeTransferAssetMapSequenceSupport'+str(number)
        current='RuntimeTransferAssetMapMaterialization'+str(number)
        imports=[current]+['RuntimeTransferAssetMapMaterialization'+str(i) for i in range(number+1,len(parts))]
        source=''.join('import ShielddSecurity.'+module+'\n' for module in imports)
        source+=f'''import ShielddSecurity.CompilerSequenceCompletion
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact metadata SHA256 {result['recipe']['checked']['metadata_sha256']}.
-- A bounded row page and at most8 deferred low-column exceptions.
def suffix : List CompilerCompletion.Step :=
  [{','.join(module+'.steps' for module in imports[1:])}].flatten
def exceptions : List Nat := {part['exceptions']}
theorem writes_checked : CompilerSequenceCompletion.checkWrites {copy} {part['floor']}
    exceptions (PoseidonCompletion.writes suffix) = true := by decide
theorem rows_checked : CompilerSequenceCompletion.checkRows {copy} {part['floor']}
    exceptions {current}.rawRows = true := by decide
theorem outside : ∀ row ∈ {current}.rawRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ PoseidonCompletion.writes suffix :=
  CompilerSequenceCompletion.frame_rows {copy} {part['floor']} exceptions
    (PoseidonCompletion.writes suffix) {current}.rawRows writes_checked rows_checked
'''
        source+=''.join('#print axioms '+export+'\n' for export in ('writes_checked','rows_checked','outside'))
        modules[name]=_signature_audits(source+'end ShielddSecurity.'+name+'\n')
    return modules


def construct_numeric(data, extracted, accepted_roles, base):
    """Execute and independently check numeric rows; never claims full-map truth."""
    result=plan(data,extracted,accepted_roles);recipe=result['recipe'];rho=dict(base)
    copy=recipe['checked']['metadata']['constant_copy'];p=relation.MODULUS
    if rho.get(copy,0)!=rho.get(0,0):
        raise relation.RelationError('map numeric constructor kept constant-copy link')
    evaluate=lambda lc:sum(rho.get(column,0)*coefficient for column,coefficient in lc)%p
    for step in recipe['steps']:
        if step['kind']=='square':
            rho[step['output']]=(evaluate(step['input'])**2-evaluate(step['remainder']))%p
        else:
            left,right=evaluate(step['left']),evaluate(step['right'])
            rho[step['output']]=(left*right-evaluate(step['remainder']))%p
            rho[step['auxiliary']]=(left-right)**2%p
    if any(evaluate(recipe['raw'][i][0])**2%p!=evaluate(recipe['raw'][i][1]) for i in result['original_partition']):
        raise relation.RelationError('map numeric original-row construction failed')
    writes={column for step in recipe['steps'] for column in step['writes']}
    if any(rho.get(column,0)!=value for column,value in base.items() if column not in writes):
        raise relation.RelationError('map numeric constructor modified unowned/seed column')
    return dict(assignment=rho,plan=result,proof=False,
                scope='all original numeric materialization rows only; native asserted phase/full map not claimed')


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    result=plan(data,extracted,accepted_roles);recipe=result['recipe'];count=len(result['parts'])
    parts=['RuntimeTransferAssetMapMaterialization'+str(i) for i in range(count)]
    supports=['RuntimeTransferAssetMapSequenceSupport'+str(i) for i in range(count)]
    copy=recipe['checked']['metadata']['constant_copy'];name='RuntimeTransferAssetMapNumericConstruction'
    source=''.join('import ShielddSecurity.'+module+'\n' for module in supports)
    source+=f'''set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- All original numeric allocation rows; native assertion phase is separate.
def modulus : Nat := {completion.maps.P}
def chunks : List (List CompilerCompletion.Step) := [{','.join(part+'.steps' for part in parts)}]
def steps : List CompilerCompletion.Step := chunks.flatten
def rawChunks : List (List Row) := [{','.join(part+'.rawRows' for part in parts)}]
def rawRows : List Row := rawChunks.flatten
def originalRowIndices : List Nat := {result['original_partition']}
def seedColumns : List Nat := {sorted(recipe['seeds'].values())}
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  CompilerCompletion.run rho steps
'''
    exports=[]
    for i in range(count):
        source+=f'def prefix{i} : List CompilerCompletion.Step := [{",".join(p+".steps" for p in parts[:i])}].flatten\n'
        source+=f'''theorem split{i} : steps = prefix{i} ++ {parts[i]}.steps ++ {supports[i]}.suffix := by
  simp only [steps,chunks,prefix{i},{supports[i]}.suffix,List.flatten_cons,List.flatten_nil,
    List.nil_append,List.append_nil,List.append_assoc]
'''
        exports.append('split'+str(i))
    source+=f'''
theorem writes_checked : CompilerSequenceCompletion.checkWrites {copy} {result['seed_floor']}
    [] (PoseidonCompletion.writes steps) = true := by decide
theorem seeds_checked : seedColumns.all (fun column => decide (column < {result['seed_floor']})) = true := by decide
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ PoseidonCompletion.writes steps) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho steps column outside
theorem seed_values {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (member : column ∈ seedColumns) : completeAssignment rho column = rho column := by
  apply preserves
  apply CompilerSequenceCompletion.frame_column {copy} {result['seed_floor']} []
    (PoseidonCompletion.writes steps) column writes_checked
  exact ⟨Or.inr (of_decide_eq_true (List.all_eq_true.mp seeds_checked column member)),by simp⟩

theorem complete {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
'''
    for i in range(count):
        source+=f'''  have linked{i} : CompilerCompletion.run rho prefix{i} {copy} =
      CompilerCompletion.run rho prefix{i} 0 := by
    rw [PoseidonCompletion.run_outside rho prefix{i} {copy} (by decide),
      PoseidonCompletion.run_outside rho prefix{i} 0 (by decide),linked]
  have local{i} := {parts[i]}.complete (CompilerCompletion.run rho prefix{i}) linked{i}
  have final{i} : Satisfies (completeAssignment rho) {parts[i]}.rawRows := by
    have carried := CompilerSequenceCompletion.preserves_rows
      ({parts[i]}.completeAssignment (CompilerCompletion.run rho prefix{i}))
      {supports[i]}.suffix {parts[i]}.rawRows local{i} {supports[i]}.outside
    simpa only [completeAssignment,{parts[i]}.completeAssignment,split{i},
      CompilerSequenceCompletion.run_append] using carried
'''
    source+='''  intro row member
  obtain ⟨chunk,present,inside⟩ := List.mem_flatten.mp member
  simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with '''+' | '.join('rfl' for _ in parts)+'\n'
    source+=''.join('  · exact final'+str(i)+' row inside\n' for i in range(count))
    exports+=['writes_checked','seeds_checked','preserves','seed_values','complete']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
