"""Construct one exact recovery secret/confirmation/stream permutation.

Only captured hash materializations are written; surrounding recovery, group,
scalar, output and other Transfer rows need separate preservation/composition.
"""
from . import transfer_recovery_hash as hashes,transfer_note_hash_join as joins,transfer_recovery_capsule as capsules
from . import generate_note_hash_block_completion as blocks,transfer_relation as relation


def generate(data,extracted,recovery_data,output_data,accepted_roles,parameter_root,on_chunk=None):
    checked=hashes.inspect_metadata(data,recovery_data,output_data,accepted_roles,parameter_root)
    selected=hashes.round_selection(data,extracted,recovery_data,output_data,accepted_roles,parameter_root)
    recovery=capsules.inspect_metadata(recovery_data,output_data,accepted_roles)
    readonly=accepted_roles.get('observed')
    if not isinstance(readonly,dict):raise relation.RelationError('recovery constructor accepted caller LCs required')
    obj=checked['metadata'];entry=recovery['metadata']['capsules'][obj['slot']]
    # Named downstream addition LCs deliberately change with their source hash.
    # Their exact native source additions were checked by the capsule ingress;
    # their supplied equality witnesses are separate, later constructive owners.
    role=obj['role'];excluded={tuple(obj['hash']['output']['source'])}
    downstream={'secret':'computed_c2','amount-stream':'computed_amount','blinding-stream':'computed_blinding'}
    if role in downstream:excluded.add(tuple(entry[downstream[role]]['source']))
    protected=[*readonly.values(),*recovery['outputs']['observed'].values(),
               *(lc for handle,lc in recovery['observed'].items() if handle not in excluded)]
    context=selected,checked,dict(metadata={},readonly_lcs=protected)
    base=f'RuntimeTransferRecovery{obj["slot"]}{obj["role"].title().replace("-","")}Hash'
    width=checked['width'];yield from joins._generate_checked([checked],[selected],base,width=width)
    chunks=[];rows=set();owned=set();support=set();expected=set(selected['rows'])
    for index,start in enumerate(range(0,65,5)):
        plan=blocks._chunk_plan(context,start,min(start+5,65))
        if set(plan['writes'])&(owned|support):raise relation.RelationError('recovery hash later writes change earlier rows')
        owned.update(plan['writes']);support.update(c for row in plan['raw'].values() for terms in row for c,_ in terms)
        rows.update(plan['raw'])
        if on_chunk is not None:on_chunk(index,plan)
        module,source=blocks._chunk_source(base,index,plan,chunks);yield module,source;chunks.append(module)
    if rows!=expected:raise relation.RelationError('recovery hash full constructor row coverage')
    role=selected['calls'][0]['role'].replace('.','_')
    yield base+'Completion',blocks._composition(base,chunks,obj,sound_namespace='RuntimeHashBlock_'+role+'_0',width=width)
