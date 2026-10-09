"""Construct actual two-block output hash rows, preserving supplied role LCs.

The separate computed-to-supplied assertion is a remaining owner join: this
constructor owns hash materializations only and never assumes that equality.
"""
from . import transfer_note_output_hash as output,transfer_note_outputs as roles,transfer_relation as relation
from . import generate_note_hash_block_completion as blocks,generate_note_hash_call_completion as calls
from .transfer_balance_rows import source_index


def _context(data,extracted,output_data,accepted_roles,parameter_root):
    accepted=roles.inspect_metadata(output_data,accepted_roles)
    checked=output.inspect_metadata(data,output_data,accepted_roles,parameter_root)
    selected=output.round_selection(data,extracted,output_data,accepted_roles,parameter_root)
    refs=[];readonly=[]
    for role in accepted['metadata']['outputs']:
        refs.extend([*role['note'],*role['capsule'],*role['payload_key'],role['commitment'],role['capsule_commitment']])
        if role['receiver_inverse'] is not None:refs.append(role['receiver_inverse'])
        readonly.extend(accepted['observed'][source_index(ref)] for ref in role['amount_bits'])
    readonly.extend(accepted['observed'][source_index(ref['source'])] for ref in refs if 'source' in ref)
    return selected,checked,dict(metadata=accepted['metadata'],readonly_lcs=readonly)


def generate(page_data,extractions,output_data,accepted_roles,parameter_root,on_chunk=None):
    checked=output.inspect_calls(page_data,output_data,accepted_roles)
    if not isinstance(extractions,(tuple,list)) or len(extractions)!=2:
        raise relation.RelationError('output completion exact two extraction inventory')
    obj=checked[0]['metadata'];base=f'RuntimeTransferOutput{obj["slot"]}{obj["role"].capitalize()}Hash'
    yield from output.generate_call(page_data,extractions,output_data,accepted_roles,parameter_root)
    prior_support=set();prior_owned=set();second_floor=None
    for block,(data,extracted) in enumerate(zip(page_data,extractions)):
        prefix=base+f'Block{block}';context=_context(data,extracted,output_data,accepted_roles,parameter_root)
        chunks=[];support=set();owned=set();selected_rows=set();expected=None
        for index,start in enumerate(range(0,65,5)):
            plan=blocks._chunk_plan(context,start,min(start+5,65));writes=set(plan['writes'])
            if writes&(prior_support|prior_owned|support|owned):
                raise relation.RelationError('output later hash writes change earlier actual rows')
            support.update(c for row in plan['raw'].values() for terms in row for c,_ in terms)
            owned.update(writes);selected_rows.update(plan['raw'])
            if expected is None:expected=set(plan['selected']['rows'])
            if on_chunk is not None:on_chunk(block,index,plan)
            module,source=blocks._chunk_source(prefix,index,plan,chunks);yield module,source;chunks.append(module)
        if selected_rows!=expected:raise relation.RelationError('output completion full exact permutation row coverage')
        if block==1 and obj['constant_copy'] not in owned:
            floor=min(owned)
            if all(c==obj['constant_copy'] or c<floor for c in prior_support):second_floor=floor
        prior_support.update(support);prior_owned.update(owned)
        permutation=f'RuntimeHashBlock_output{obj["slot"]}_{obj["role"]}{obj["level"]}_permutation{block}_0'
        yield prefix+'Completion',blocks._composition(prefix,chunks,obj,rows_only=True,
            sound_module=prefix+'_Composition',sound_namespace=permutation)
    yield base+'Completion',calls._composition(base,obj,second_floor=second_floor,role_prefix='output')
