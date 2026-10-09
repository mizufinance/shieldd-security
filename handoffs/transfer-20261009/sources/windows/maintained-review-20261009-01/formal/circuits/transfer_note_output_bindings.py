"""Construct the exact computed-to-supplied output hash assertion witness.

Uses the accepted typed NOTE/recovery page and physical row extraction. Other
owner rows survive only after their supports are proved disjoint separately.
"""
from . import transfer_note_output_hash as hashes,transfer_note_outputs as outputs,transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import source_index,combine,canonical
from .generate_hash_round import linear,_signature_audits


def plan(data,extracted,output_data,accepted_roles):
    checked=hashes.inspect_boundaries(data,output_data,accepted_roles)
    roles=outputs.inspect_metadata(output_data,accepted_roles);obj=checked['metadata'];copy=obj['constant_copy']
    raw,normalized=arithmetic.normalize_selection(extracted,obj,checked['metadata_sha256'])
    computed=checked['observed'][source_index(obj['hash']['output']['source'])]
    target_ref=source_index(obj['supplied_commitment']['source']);target_lc=checked['observed'][target_ref]
    if target_ref[0]!=1 or target_lc!=((target_ref[1]+3,1),):
        raise relation.RelationError('output binding exact supplied unit witness required')
    target=target_lc[0][0]
    delta=combine(computed,target_lc,-1);opposite=canonical((c,-v) for c,v in delta)
    matched=[i for i,row in normalized.items() if row in ((delta,()),(opposite,()))]
    links=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(matched)!=1 or len(links)!=1 or set(raw)!=set(matched+links):
        raise relation.RelationError('output binding exact assertion/copy row coverage')
    readonly={0,1,2,copy}
    for handle,terms in roles['observed'].items():
        if handle!=target_ref:readonly.update(c for c,_ in terms)
    for terms in accepted_roles['observed'].values():readonly.update(c for c,_ in terms)
    for ref in obj['hash']['inputs']:
        if 'source' in ref:readonly.update(c for c,_ in checked['observed'][source_index(ref['source'])])
    if target in readonly or any(c==target for c,_ in computed):
        raise relation.RelationError('output binding target aliases shared/readonly/source column')
    return dict(checked=checked,computed=computed,target=target,copy=copy,raw_row=raw[matched[0]],
        original_row=matched[0],kept=sorted(readonly),writes=[target],scope='one output hash supplied witness; surrounding rows require separate support proof')


def generate(data,extracted,output_data,accepted_roles):
    selected=plan(data,extracted,output_data,accepted_roles);obj=selected['checked']['metadata']
    name=f'RuntimeTransferOutput{obj["slot"]}{obj["role"].capitalize()}HashBindingCompletion'
    return _source(selected,name)


def capsule_copy_plan(data,extracted,accepted_roles,slot):
    slot=relation.natural(slot,2);selected=outputs.certificates(data,extracted,accepted_roles)
    checked=selected['checked'];obj=checked['metadata'];copy=obj['constant_copy']
    computed,target_lc=selected['bindings'][2*slot+1]
    target_ref=source_index(obj['outputs'][slot]['note'][7]['source'])
    if target_ref[0]!=1 or target_lc!=((target_ref[1]+3,1),):
        raise relation.RelationError('capsule NOTE recovery exact unit target witness required')
    target=target_lc[0][0];delta=combine(computed,target_lc,-1)
    matches=[i for i,row in selected['rows'].items() if row in ((delta,()),(canonical((c,-v) for c,v in delta),()))]
    if len(matches)!=1:raise relation.RelationError('capsule NOTE recovery exact original assertion missing')
    readonly={0,1,2,copy}
    for handle,terms in checked['observed'].items():
        if handle!=target_ref:readonly.update(c for c,_ in terms)
    for terms in accepted_roles['observed'].values():readonly.update(c for c,_ in terms)
    if target in readonly or any(c==target for c,_ in computed):
        raise relation.RelationError('capsule NOTE recovery target aliases shared/source column')
    return dict(checked=checked,computed=computed,target=target,copy=copy,raw_row=selected['raw'][matches[0]],
        original_row=matches[0],kept=sorted(readonly),writes=[target],
        scope='one supplied capsule commitment copied to exact NOTE recovery witness; surrounding rows separate')


def generate_capsule_copy(data,extracted,accepted_roles,slot):
    selected=capsule_copy_plan(data,extracted,accepted_roles,slot)
    return _source(selected,f'RuntimeTransferOutput{slot}RecoveryInputBindingCompletion')


def _source(selected,name):
    obj=selected['checked']['metadata']
    left,right=selected['raw_row'];target=selected['target'];copy=selected['copy']
    source=f'''import ShielddSecurity.LinearBindingCompletion
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact original assertion row {selected['original_row']} of relation {obj['relation_digest']}.
-- Only supplied witness {target} is owned; hash/capsule meaning and surrounding rows separate.
def modulus : Nat := {relation.MODULUS}
def computed : Linear := {linear(selected['computed'])}
def supplied : Linear := [({target},1)]
def ownedWrites : List Nat := [{target}]
def kept : List Nat := {selected['kept']}
def rawRow : Row := ⟨{linear(left)},{linear(right)}⟩
def rawRows : List Row := [rawRow]
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  LinearBindingCompletion.assignment rho computed {target}
theorem fresh_checked : computed.all (fun term => decide (term.1 ≠ {target})) = true := by decide
theorem kept_checked : kept.all (fun column => decide (column ≠ {target})) = true := by decide
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
  apply LinearBindingCompletion.preserves
  simpa only [ownedWrites,List.mem_singleton] using outside
theorem value {{F : Type}} [Field F] (rho : Nat → F) :
    completeAssignment rho {target} = eval rho computed := LinearBindingCompletion.value rho computed {target}
theorem binding {{F : Type}} [Field F] (rho : Nat → F) :
    eval (completeAssignment rho) computed = eval (completeAssignment rho) supplied := by
  have unchanged := LinearBindingCompletion.eval_preserves rho computed computed {target} (by
    intro term member
    exact of_decide_eq_true ((List.all_eq_true.mp fresh_checked) term member))
  simpa only [supplied,eval,Int.cast_one,one_mul,add_zero,value] using unchanged
theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  intro row member
  simp only [rawRows,List.mem_singleton] at member
  subst row
  apply LinearBindingCompletion.original_complete rho computed {target} {copy} rawRow
  · intro term member
    exact of_decide_eq_true ((List.all_eq_true.mp fresh_checked) term member)
  · decide
  · decide
  · exact linked
  · decide
  · decide
'''
    for export in ('fresh_checked','kept_checked','preserves','value','binding','complete_rows'):
        source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
