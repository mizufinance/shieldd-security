"""Strict finite column correspondence for already accepted note hash cones.

This is an optional reuse boundary, not a hash-identity or native-path claim.
Every source DAG, domain/arity, parameter and original-row check precedes it.
Unsupported folded constants, fused LCs or allocation orders are refused.
"""
from . import generate_note_hash_block_completion as blocks,transfer_relation as relation
from . import generate_note_hash_completion as rounds
from .generate_hash_round import linear,_signature_audits


def suffix_plan(source_data,source_extraction,actual_data,actual_extraction,
                note_data,accepted_roles,parameter_root,start=2,stop=65):
    source=blocks._context(source_data,source_extraction,note_data,accepted_roles,parameter_root)
    actual=blocks._context(actual_data,actual_extraction,note_data,accepted_roles,parameter_root)
    return _from_contexts(source,actual,start,stop)


def _from_contexts(source,actual,start,stop):
    start=relation.natural(start,65);stop=relation.natural(stop,66)
    if not start<stop<=65:
        raise relation.RelationError('hash renaming requires an ascending nonempty suffix')
    left_call=source[0]['calls'][0];right_call=actual[0]['calls'][0]
    if left_call['parameters']!=right_call['parameters']:
        raise relation.RelationError('hash renaming exact round parameters differ')
    columns={};inverse={};source_rows={};actual_rows={};row_pairs=[]
    source_writes=[];actual_writes=[]
    def column(left,right):
        if (left in columns and columns[left]!=right) or (right in inverse and inverse[right]!=left):
            raise relation.RelationError('hash renaming column alias/inconsistent correspondence')
        columns[left]=right;inverse[right]=left
    def linear(left,right):
        if len(left)!=len(right) or any(a[1]!=b[1] for a,b in zip(left,right)):
            raise relation.RelationError('hash renaming exact LC coefficients/shape differ')
        for a,b in zip(left,right):column(a[0],b[0])
    column(0,0)
    column(source[1]['metadata']['constant_copy'],actual[1]['metadata']['constant_copy'])
    for index in range(start,stop):
        a=rounds._from_checked(*source,index);b=rounds._from_checked(*actual,index)
        for key in ('before','after'):
            for left,right in zip(a['segment'][key],b['segment'][key]):linear(left,right)
        if len(a['steps'])!=len(b['steps']):
            raise relation.RelationError('hash renaming materialization inventory differs')
        for left,right in zip(a['steps'],b['steps']):
            if left['kind']!=right['kind']:
                raise relation.RelationError('hash renaming materialization constructors differ')
            for key in ('left','right','remainder'):linear(left[key] or (),right[key] or ())
            column(left['output'],right['output'])
            if left['kind']=='product':column(left['auxiliary'],right['auxiliary'])
        if len(a['raw'])!=len(b['raw']):
            raise relation.RelationError('hash renaming exact original row inventory differs')
        for (i,left),(j,right) in zip(a['raw'].items(),b['raw'].items()):
            linear(left[0],right[0]);linear(left[1],right[1])
            if i in source_rows and source_rows[i]!=left or j in actual_rows and actual_rows[j]!=right:
                raise relation.RelationError('hash renaming repeated original row differs')
            source_rows[i]=left;actual_rows[j]=right;row_pairs.append((i,j))
        source_writes.extend(a['writes']);actual_writes.extend(b['writes'])
    if len(set(source_writes))!=len(source_writes) or len(set(actual_writes))!=len(actual_writes):
        raise relation.RelationError('hash renaming repeated owned column')
    if [columns[c] for c in source_writes]!=actual_writes:
        raise relation.RelationError('hash renaming exact owned-write correspondence differs')
    # This exact equality is the kernel receipt to emit, not a semantic claim
    # established by the Python check. Both term order and coefficients survive.
    for i,j in row_pairs:
        renamed=tuple(tuple((columns[c],v) for c,v in terms) for terms in source_rows[i])
        if renamed!=actual_rows[j]:
            raise relation.RelationError('hash renaming original row correspondence failed')
    return dict(start=start,stop=stop,columns=sorted(columns.items()),
        source_writes=source_writes,actual_writes=actual_writes,
        source_rows=source_rows,actual_rows=actual_rows,row_pairs=row_pairs,
        source_before=left_call['segments'][start]['before'],
        actual_before=right_call['segments'][start]['before'],
        source_after=left_call['segments'][stop-1]['after'],
        actual_after=right_call['segments'][stop-1]['after'],
        scope='exact finite hash suffix column/LC/row correspondence; kernel transport unrun')


def generate_chunk(source_data,source_extraction,actual_data,actual_extraction,
                   note_data,accepted_roles,parameter_root,index):
    """Emit one actual five-round construction reusing a checked source chunk.

Prefix chunk0 stays independent: domain/arity/level constant folding is not a
column substitution. Shared chunks1..12 require their source kernel exports.
"""
    index=relation.natural(index,13)
    if not index:raise relation.RelationError('hash renaming folded prefix chunk is not reusable')
    source=blocks._context(source_data,source_extraction,note_data,accepted_roles,parameter_root)
    actual=blocks._context(actual_data,actual_extraction,note_data,accepted_roles,parameter_root)
    a=source[1]['metadata'];b=actual[1]['metadata']
    if a['role']!='state' or b['role']!='state':
        raise relation.RelationError('hash renaming generated reuse currently owns state-tree chunks only')
    plan=_from_contexts(source,actual,5*index,min(5*index+5,65))
    source_module=f'RuntimeNoteHash{a["slot"]}State{a["level"]}CompletionChunk{index}'
    name=f'RuntimeNoteHash{b["slot"]}State{b["level"]}RenamedCompletionChunk{index}'
    rendered=lambda rows:',\n'.join('  ⟨'+linear(left)+','+linear(right)+'⟩' for _,(left,right) in sorted(rows.items()))
    vectors=lambda lcs:'['+', '.join(linear(lc) for lc in lcs)+']'
    out=f'''import ShielddSecurity.RowCompletionRenaming
import ShielddSecurity.{source_module}
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact source/parameter/LC/original-row correspondence, rounds {plan['start']}..{plan['stop']-1}.
-- Native tree prefix and complete Transfer remain separate open joins.
def columns : Nat → Nat := fun column => match column with
'''
    for left,right in plan['columns']:out+=f'  | {left} => {right}\n'
    out+='  | _ => column\ndef inverse : Nat → Nat := fun column => match column with\n'
    for left,right in sorted(plan['columns'],key=lambda pair:pair[1]):out+=f'  | {right} => {left}\n'
    out+=f'''  | _ => column
def ownedWrites : List Nat := {plan['actual_writes']}
def rawRows : List Row := [
{rendered(plan['actual_rows'])}]
def sourceBefore : List Linear := {vectors(plan['source_before'])}
def actualBefore : List Linear := {vectors(plan['actual_before'])}
def sourceAfter : List Linear := {vectors(plan['source_after'])}
def actualAfter : List Linear := {vectors(plan['actual_after'])}
def constructed {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  {source_module}.completeAssignment (fun column => rho (columns column))
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  RowCompletionRenaming.assignment rho (constructed rho) columns inverse {source_module}.ownedWrites

theorem owned_checked : {source_module}.ownedWrites.map columns = ownedWrites := by decide
theorem rows_checked : rawRows = {source_module}.rawRows.map (RowRenaming.row columns) := by decide
theorem inverse_rows_checked : {source_module}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (inverse (columns term.1) = term.1))) = true := by decide
theorem inverse_writes_checked : {source_module}.ownedWrites.all
    (fun column => decide (inverse (columns column) = column)) = true := by decide
theorem interface_checked : actualBefore = sourceBefore.map (RowRenaming.linear columns) ∧
    actualAfter = sourceAfter.map (RowRenaming.linear columns) := by decide
theorem inverse_interface_checked : (sourceBefore ++ sourceAfter).all (fun terms => terms.all
    (fun term => decide (inverse (columns term.1) = term.1))) = true := by decide

theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
  apply RowCompletionRenaming.assignment_preserves
  simpa only [owned_checked] using outside

theorem complete_rows {{F : Type}} [Field F] [CharP F {source_module}.modulus] (rho : Nat → F)
    (linked : rho {b['constant_copy']} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have sourceLink : (fun column => rho (columns column)) {a['constant_copy']} =
      (fun column => rho (columns column)) 0 := by
    change rho {b['constant_copy']} = rho 0
    exact linked
  apply RowCompletionRenaming.complete_rows rho (constructed rho) columns inverse
    {source_module}.ownedWrites {source_module}.rawRows rawRows rows_checked
  · intro row member term present
    exact of_decide_eq_true ((List.all_eq_true.mp
      ((List.all_eq_true.mp inverse_rows_checked) row member)) term present)
  · intro column member
    exact of_decide_eq_true ((List.all_eq_true.mp inverse_writes_checked) column member)
  · intro column outside
    exact {source_module}.preserves (fun column => rho (columns column)) column outside
  · exact {source_module}.complete (fun column => rho (columns column)) sourceLink

theorem before_values {{F : Type}} [Field F] (rho : Nat → F) :
    actualBefore.map (eval rho) = sourceBefore.map (eval (fun column => rho (columns column))) := by
  rw [interface_checked.1, List.map_map]
  apply List.map_congr_left
  intro terms member
  exact RowRenaming.eval_linear rho columns terms

theorem after_values {{F : Type}} [Field F] (rho : Nat → F) :
    actualAfter.map (eval (completeAssignment rho)) = sourceAfter.map (eval (constructed rho)) := by
  rw [interface_checked.2, List.map_map]
  apply List.map_congr_left
  intro terms member
  change eval (completeAssignment rho) (RowRenaming.linear columns terms) = eval (constructed rho) terms
  rw [RowRenaming.eval_linear]
  apply eval_agrees
  intro term present
  apply RowCompletionRenaming.assignment_at rho (constructed rho) columns inverse
    {source_module}.ownedWrites term.1
  · exact of_decide_eq_true ((List.all_eq_true.mp
      ((List.all_eq_true.mp inverse_interface_checked) terms (List.mem_append_right sourceBefore member))) term present)
  · intro column owned
    exact of_decide_eq_true ((List.all_eq_true.mp inverse_writes_checked) column owned)
  · intro column outside
    exact {source_module}.preserves (fun column => rho (columns column)) column outside
'''
    for export in ('owned_checked','rows_checked','inverse_rows_checked','inverse_writes_checked',
        'interface_checked','inverse_interface_checked','preserves','complete_rows','before_values','after_values'):
        out+=f'#print axioms {export}\n'
    return name,_signature_audits(out+f'end ShielddSecurity.{name}\n')


def generate_sound_chunk(source_data,source_extraction,actual_data,actual_extraction,
                         note_data,accepted_roles,parameter_root,index):
    """Transport exact native round soundness, independently of construction.

    The actual parameter literals, row lists and coordinate LCs are emitted as
    checked data. Prefix folding is still refused; no actual Data module or
    actual fifth-power arithmetic certificate is required for this suffix.
    """
    from .generate_hash_round import finite_function,signed
    index=relation.natural(index,13)
    if not index:raise relation.RelationError('hash renaming folded prefix chunk is not reusable')
    source=blocks._context(source_data,source_extraction,note_data,accepted_roles,parameter_root)
    actual=blocks._context(actual_data,actual_extraction,note_data,accepted_roles,parameter_root)
    a=source[1]['metadata'];b=actual[1]['metadata']
    if a['role']!='state' or b['role']!='state':
        raise relation.RelationError('hash renaming generated reuse currently owns state-tree chunks only')
    source_base=f'RuntimeNoteHash{a["slot"]}State{a["level"]}Block{a["block"]}'
    name=f'RuntimeNoteHash{b["slot"]}State{b["level"]}RenamedSoundChunk{index}'
    return _sound_chunk_context(source,actual,index,source_base,name)


def _sound_chunk_context(source,actual,index,source_base,name):
    """Internal emitter after each component's full typed/native/row ingress."""
    from .generate_hash_round import finite_function,signed
    index=relation.natural(index,13)
    if not index:raise relation.RelationError('hash renaming folded prefix chunk is not reusable')
    _module_name(source_base);_module_name(name)
    a=source[1]['metadata']
    plan=_from_contexts(source,actual,5*index,min(5*index+5,65))
    start,stop=plan['start'],plan['stop']
    source_namespace='RuntimeHashBlock_'+source[0]['calls'][0]['role'].replace('.','_')+'_0'
    params=actual[0]['calls'][0]['parameters'];width=params['width']
    out=f"""import ShielddSecurity.RowRenaming
import ShielddSecurity.{source_base}_Rounds_{start}_{stop-1}
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact actual source/parameter/LC/original-row substitution; native prefix remains independent.
-- The source extraction and actual extraction both pass the complete bounded native DAG matcher.
def modulus : Nat := {relation.MODULUS}
def columns : Nat → Nat := fun column => match column with
"""
    for left,right in plan['columns']:out+=f'  | {left} => {right}\n'
    out+='  | _ => column\n'
    out+=f'def parameters : Poseidon.Parameters Int {width} where\n  ark := fun index => match index with\n'
    for i,values in enumerate(params['ark']):
        out+=f'    | {i} => '+finite_function(values,lambda v:str(signed(v)),'0').replace('\n','\n    ')+'\n'
    out+='    | _ => fun _ => 0\n  mds := fun row => match row.val with\n'
    for i,values in enumerate(params['mds']):
        out+=f'    | {i} => '+finite_function(values,lambda v:str(signed(v)),'0').replace('\n','\n    ')+'\n'
    out+='    | _ => fun _ => 0\n'
    out+=f'theorem parameters_checked : parameters = {source_namespace}.parameters := by rfl\n'
    exports=['parameters_checked']
    for i in range(start,stop):
        local=rounds._from_checked(*actual,i)
        body=',\n'.join('  ⟨'+linear(left)+','+linear(right)+'⟩' for left,right in local['raw'].values())
        out+=f'def rawRows{i} : List Row := [\n{body}]\n'
        for key in ('before','after'):
            out+=f'def {key}{i} : Poseidon.State Linear {width} :=\n  '+finite_function(
                local['segment'][key],linear,'[]').replace('\n','\n  ')+'\n'
        out+=f"""
theorem rows_checked_{i} : rawRows{i} = ({source_namespace}.rawRoundRows {i}).map
    (RowRenaming.row columns) := by decide

theorem interface_checked_{i} : ∀ coordinate : Fin {width},
    before{i} coordinate = RowRenaming.linear columns ({source_namespace}.states {i} coordinate) ∧
    after{i} coordinate = RowRenaming.linear columns ({source_namespace}.states {i+1} coordinate) := by decide

theorem round_sound_{i} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows{i}) :
    (fun coordinate => eval rho (after{i} coordinate)) =
      Poseidon.round (Poseidon.castParameters parameters) {i}
        (fun coordinate => eval rho (before{i} coordinate)) := by
  let pulled := fun column => rho (columns column)
  have sourceSatisfied : Satisfies pulled ({source_namespace}.rawRoundRows {i}) := by
    apply RowRenaming.satisfied_rows rho columns ({source_namespace}.rawRoundRows {i}) rawRows{i}
    · intro row member
      rw [rows_checked_{i}]
      exact List.mem_map.mpr ⟨row,member,rfl⟩
    · exact satisfied
  have sourceOne : pulled 0 = 1 := by
    change rho 0 = 1
    exact one
  have four : (4 : F) ≠ 0 := by
    intro zero
    have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  have normalized : Satisfies pulled ({source_namespace}.roundRows {i}) :=
    Compiler.unoutline_rows_sound pulled {a['constant_copy']} ({source_namespace}.rawRoundRows {i})
      sourceSatisfied {source_namespace}.constant_link_{i}
  have beforeValues : (fun coordinate => eval rho (before{i} coordinate)) =
      (fun coordinate => eval pulled ({source_namespace}.states {i} coordinate)) := by
    funext coordinate
    rw [(interface_checked_{i} coordinate).1]
    exact RowRenaming.eval_linear rho columns _
  have afterValues : (fun coordinate => eval rho (after{i} coordinate)) =
      (fun coordinate => eval pulled ({source_namespace}.states {i+1} coordinate)) := by
    funext coordinate
    rw [(interface_checked_{i} coordinate).2]
    exact RowRenaming.eval_linear rho columns _
  rw [afterValues,beforeValues,parameters_checked]
  exact Poseidon.round_certificate_sound pulled ({source_namespace}.roundRows {i})
    {source_namespace}.parameters {i} ({source_namespace}.states {i})
    ({source_namespace}.shifted {i}) ({source_namespace}.transformed {i})
    ({source_namespace}.states {i+1}) sourceOne four normalized {source_namespace}.certificate_{i}
"""
        exports.extend(f'{key}_{i}' for key in ('rows_checked','interface_checked','round_sound'))
    for export in exports:out+=f'#print axioms {export}\n'
    return name,_signature_audits(out+f'end ShielddSecurity.{name}\n')


def generate_preservation(source_data,source_extraction,actual_data,actual_extraction,
                          note_data,accepted_roles,parameter_root,index):
    """Sequence a renamed constructor against its exact earlier actual chunks.

    A numeric fence is checked over captured prior supports before emitting.
    The kernel scans those imported row lists once, and preserves each row by
    the constructor's exported outside-column equality. Allocation shapes that
    cannot satisfy this exact fence are refused rather than assumed monotone.
    """
    index=relation.natural(index,13)
    if not index:raise relation.RelationError('hash renaming folded prefix chunk is not reusable')
    source=blocks._context(source_data,source_extraction,note_data,accepted_roles,parameter_root)
    actual=blocks._context(actual_data,actual_extraction,note_data,accepted_roles,parameter_root)
    a=source[1]['metadata'];b=actual[1]['metadata']
    if a['role']!='state' or b['role']!='state':
        raise relation.RelationError('hash renaming generated reuse currently owns state-tree chunks only')
    plan=_from_contexts(source,actual,5*index,min(5*index+5,65))
    copy=b['constant_copy'];floor=min(plan['actual_writes'])
    earlier=sorted({row for segment in actual[0]['calls'][0]['segments'][:5*index]
                    for row in segment['rows']}|{actual[0]['constant_link']})
    if copy in plan['actual_writes'] or any(c!=copy and c>=floor for row in earlier
            for terms in actual[0]['rows'][row] for c,_ in terms):
        raise relation.RelationError('hash renaming actual prior-row column fence unsupported')
    base=f'RuntimeNoteHash{b["slot"]}State{b["level"]}'
    owner=base+f'RenamedCompletionChunk{index}';name=base+f'RenamedCompletionStage{index}'
    prior=[base+'CompletionChunk0']+[base+f'RenamedCompletionStage{i}' for i in range(1,index)]
    out='import ShielddSecurity.ColumnFence\nimport ShielddSecurity.'+owner+'\n'
    out+=''.join('import ShielddSecurity.'+module+'\n' for module in prior)
    out+=f"""set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact earlier actual chunk rows; no assertion that arbitrary other Transfer rows survive.
abbrev rawRows := {owner}.rawRows
abbrev ownedWrites := {owner}.ownedWrites
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  {owner}.completeAssignment rho

theorem complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows :=
  {owner}.complete_rows rho linked

theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  {owner}.preserves rho column outside
def priorRows : List Row := {' ++ '.join(module+'.rawRows' for module in prior)}

theorem writes_lower_checked : ColumnFence.checkWrites {copy} {floor} ownedWrites = true := by decide
theorem prior_upper_checked : ColumnFence.checkRows {copy} {floor} priorRows = true := by decide

theorem prior_preserved {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho priorRows) : Satisfies (completeAssignment rho) priorRows := by
  have absent := ColumnFence.checked_rows {copy} {floor} ownedWrites priorRows
    writes_lower_checked prior_upper_checked
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (completeAssignment rho) terms = eval rho terms := by
    apply eval_agrees
    intro term found
    exact preserves rho term.1 (absent row member term (included term found))
  rw [agrees row.a (by intro term found; exact List.mem_append_left row.b found),
      agrees row.b (by intro term found; exact List.mem_append_right row.a found)]
  exact satisfied row member
"""
    for export in ('complete','preserves','writes_lower_checked','prior_upper_checked','prior_preserved'):
        out+=f'#print axioms {export}\n'
    return name,_signature_audits(out+f'end ShielddSecurity.{name}\n')


def generate_compact_sound(source_data,source_extraction,actual_data,actual_extraction,
                           note_data,accepted_roles,parameter_root):
    """Compose actual prefix plus checked renamed suffix without actual Data.

    Five independent prefix certificates retain native folding. Twelve bounded
    suffix receipts use the accepted source's native round certificates. The
    composition defines states through those imported interfaces and uses a
    symbolic recurrence; no full actual linear-data table is generated.
    """
    from .generate_hash_round import generate_selected_round
    source=blocks._context(source_data,source_extraction,note_data,accepted_roles,parameter_root)
    actual=blocks._context(actual_data,actual_extraction,note_data,accepted_roles,parameter_root)
    obj=actual[1]['metadata'];a=source[1]['metadata']
    if obj['role']!='state' or a['role']!='state':
        raise relation.RelationError('compact native composition currently owns actual state-tree permutations')
    source_base=f'RuntimeNoteHash{a["slot"]}State{a["level"]}Block{a["block"]}'
    base=f'RuntimeNoteHash{obj["slot"]}State{obj["level"]}Block{obj["block"]}'
    suffix_base=f'RuntimeNoteHash{obj["slot"]}State{obj["level"]}RenamedSoundChunk'
    internal='RuntimeHashBlock_'+actual[0]['calls'][0]['role'].replace('.','_')+'_0'
    yield from generate_compact_sound_context(source,actual,source_base,base,suffix_base=suffix_base,
                                             composition_namespace=internal)


def _module_name(name):
    if not isinstance(name,str) or not name.isascii() or not name.isidentifier():
        raise relation.RelationError('hash renaming exact Lean module identifier required')


def generate_template_context(context,base):
    """Emit exact native65 source certificates for an independently replayed template.

Kernel qualification is mandatory before any renamed consumer can import these
modules. A template receipt hash or successful Python row selection is not a
native round certificate. Every consumer independently rechecks all parameters,
source-domain/arity links and physical row/LC correspondence before generation.
"""
    from .generate_hash_round import generate_selected_block,split_block_modules
    _module_name(base)
    selected,checked,_=context
    if len(selected['calls'])!=1 or selected['calls'][0]['parameters']['width'] not in (3,6):
        raise relation.RelationError('compact template one width3/6 permutation required')
    role=selected['calls'][0]['role']
    source=generate_selected_block(checked['metadata'],selected,role,0,
                                  checked['metadata_sha256'],permutation_only=True)
    return split_block_modules(source,base,5)


def generate_compact_sound_context(source,actual,source_base,base,*,suffix_base=None,composition_namespace=None):
    """General bounded sound transport for independently inspected page contexts.

The actual ingress recipe obtains contexts using each component's own complete
domain/arity/source/native parameter matcher and independent full ordered row
selection. This entry point creates no such acceptance. The exact source module
and all12 suffix imports must separately pass kernel audits in the same stage.
Prefix folding is certified independently; every suffix row and LC is checked
by finite column correspondence. No schema, role, parameter or flag is changed.
"""
    from .generate_hash_round import generate_selected_round
    _module_name(source_base);_module_name(base)
    suffix_base=base+'RenamedSoundChunk' if suffix_base is None else suffix_base
    _module_name(suffix_base)
    internal=base+'_Compact' if composition_namespace is None else composition_namespace
    _module_name(internal)
    obj=actual[1]['metadata']
    if actual[0]['calls'][0]['parameters']['width'] not in (3,6):
        raise relation.RelationError('compact native composition width3/6 required')
    _from_contexts(source,actual,5,65)
    role=actual[0]['calls'][0]['role'];width=actual[0]['calls'][0]['parameters']['width']
    prefix=[];suffix=[]
    for i in range(5):
        module=base+f'PrefixRound{i}Sound';namespace='RuntimeHashRound_'+role.replace('.','_')+f'_0_{i}'
        prefix.append((module,namespace))
        yield module,generate_selected_round(obj,actual[0],role,0,i,actual[1]['metadata_sha256'])
    for i in range(1,13):
        module,body=_sound_chunk_context(source,actual,i,source_base,suffix_base+str(i))
        suffix.append(module);yield module,body
    # The bounded row/LC/source correspondence was rechecked by each emitter.
    # All interfaces must be the actual adjacent canonical LC lists.
    segments=actual[0]['calls'][0]['segments']
    if any(segments[i]['after']!=segments[i+1]['before'] for i in range(64)):
        raise relation.RelationError('compact native composition actual adjacent LC mismatch')
    out='import ShielddSecurity.PoseidonRoundComposition\n'
    out+=''.join('import ShielddSecurity.'+m+'\n' for m,_ in prefix)
    out+=''.join('import ShielddSecurity.'+m+'\n' for m in suffix)
    out+=f'''set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{internal}
-- Full65 actual native recurrence; prefix folding and actual suffix correspondence are checked independently.
-- Relation {obj['relation_digest']}. No actual wide Data declaration or hash-identity premise.
def modulus : Nat := {relation.MODULUS}
abbrev parameters := {suffix[0]}.parameters
'''
    def owner(i):return prefix[i][1] if i<5 else suffix[i//5-1]
    def interface(i,key):return owner(i)+'.'+key+(str(i) if i>=5 else '')
    for key,kind in (('before','Poseidon.State Linear '+str(width)),('after','Poseidon.State Linear '+str(width)),('rawRoundRows','List Row')):
        out+=f'def {key} : Nat → {kind} := fun index => match index with\n'
        for i in range(65):out+=f'  | {i} => '+(interface(i,key) if key!='rawRoundRows' else owner(i)+('.rawRows' if i<5 else f'.rawRows{i}'))+'\n'
        out+='  | _ => '+('[]' if key=='rawRoundRows' else 'fun _ => []')+'\n'
    out+=f'''def states : Nat → Poseidon.State Linear {width}
  | 0 => before 0
  | index+1 => after index
def rawRows : List Row := (List.range 65).flatMap rawRoundRows
theorem interfaces : ∀ index : Fin 65, states index.val = before index.val ∧
    states (index.val+1) = after index.val := by
  '''
    for i in range(65):
        indent='  '+'  '*i
        out+='refine Fin.cases ?_ ?_\n'+indent+'· exact ⟨rfl,rfl⟩\n'+indent+'· '
    out+='intro impossible; exact Fin.elim0 impossible\n'
    out+=f'''theorem transitions {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) : ∀ index : Fin 65,
    Satisfies rho (rawRoundRows index.val) →
      (fun column => eval rho (states (index.val+1) column)) =
        Poseidon.round (Poseidon.castParameters parameters) index.val
          (fun column => eval rho (states index.val column)) := by
  '''
    for i in range(65):
        indent='  '+'  '*i;own=owner(i)
        out+='refine Fin.cases ?_ ?_\n'+indent+'· intro satisfied\n'
        if i<5:
            out+=indent+f'  have result := {own}.actual_round_sound rho one satisfied\n'
            out+=indent+f'  have ark : {own}.parameters.ark {i} = parameters.ark {i} := rfl\n'
            out+=indent+f'  have mds : {own}.parameters.mds = parameters.mds := rfl\n'
            out+=indent+f'  rw [PoseidonRoundComposition.cast_round_agrees {own}.parameters parameters {i}\n'
            out+=indent+f'    (fun column => eval rho ({own}.before column)) ark mds] at result\n'
        else:
            out+=indent+f'  have result := {own}.round_sound_{i} rho one satisfied\n'
            out+=indent+f'  have same : {own}.parameters = parameters := rfl\n'
            out+=indent+'  rw [same] at result\n'
        out+=indent+f'  change (fun column => eval rho (after {i} column)) =\n'
        out+=indent+f'    Poseidon.round (Poseidon.castParameters parameters) {i} (fun column => eval rho (before {i} column)) at result\n'
        out+=indent+f'  simpa only [(interfaces ⟨{i},by decide⟩).1,(interfaces ⟨{i},by decide⟩).2] using result\n'
        out+=indent+'· '
    out+='intro impossible; exact Fin.elim0 impossible\n'
    out+=f'''theorem permutation_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    (fun column => eval rho (states 65 column)) =
      Poseidon.permute (Poseidon.castParameters parameters) (fun column => eval rho (states 0 column)) := by
  apply Poseidon.rounds_chain (Poseidon.castParameters parameters) (fun index column => eval rho (states index column)) 65
  intro index bound
  apply transitions rho one ⟨index,bound⟩
  intro row member
  exact satisfied row (List.mem_flatMap.mpr ⟨index,List.mem_range.mpr bound,member⟩)
'''
    for export in ('interfaces','transitions','permutation_sound'):out+=f'#print axioms {export}\n'
    yield base+'_Composition',_signature_audits(out+f'end ShielddSecurity.{internal}\n')
