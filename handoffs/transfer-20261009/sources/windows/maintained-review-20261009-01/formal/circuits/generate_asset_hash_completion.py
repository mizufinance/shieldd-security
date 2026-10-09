"""Construct exact ASSET_GENERATOR26/1 rows and map-u field value.

Only hash materializations are owned. Map/codec rows and all other Transfer
components remain separate constructive owners.
"""
from . import transfer_asset_hash as hashes,transfer_note_hash_join as joins
from . import generate_note_hash_block_completion as blocks,transfer_relation as relation


def generate(data,extracted,map_data,accepted_roles,parameter_root,on_chunk=None,*,base='RuntimeTransferAssetHash'):
    from .transfer_note_hash_renaming import _module_name
    _module_name(base)
    checked=hashes.inspect_metadata(data,map_data,accepted_roles,parameter_root)
    selected=hashes.round_selection(data,extracted,map_data,accepted_roles,parameter_root)
    readonly=accepted_roles.get('observed')
    if not isinstance(readonly,dict):raise relation.RelationError('asset hash constructor accepted caller LCs required')
    context=selected,checked,dict(metadata={},readonly_lcs=list(readonly.values()))
    yield from joins._generate_checked([checked],[selected],base,width=3)
    chunks=[];rows=set();owned=set();support=set();expected=set(selected['rows'])
    for index,start in enumerate(range(0,65,5)):
        plan=blocks._chunk_plan(context,start,min(start+5,65))
        if set(plan['writes'])&(owned|support):raise relation.RelationError('asset hash later writes change earlier rows')
        owned.update(plan['writes']);support.update(c for row in plan['raw'].values() for terms in row for c,_ in terms)
        rows.update(plan['raw'])
        if on_chunk is not None:on_chunk(index,plan)
        module,source=blocks._chunk_source(base,index,plan,chunks);yield module,source;chunks.append(module)
    if rows!=expected:raise relation.RelationError('asset hash constructor incomplete full actual row coverage')
    yield base+'Completion',blocks._composition(base,chunks,checked['metadata'],
        sound_namespace='RuntimeHashBlock_balance0_asset0_permutation0_0',width=3,
        permutation_namespace='RuntimeHashBlock_balance0_asset0_permutation0_0')
