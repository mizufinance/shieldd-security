"""Construct actual IVK/RNK permutation rows before the authorization prefix.

Typed IVK source/parameter acceptance or RNK physical recurrence acceptance is
mandatory. The existing bounded arithmetic constructor emits thirteen small
chunks and a rows-only composition. No note observer schema is manufactured.
These candidates do not construct reduction, ownership, or a full Transfer.
"""
import copy,json
from . import transfer_ivk_rows as ivk,transfer_rnk_hash as rnk,hash_rows
from . import generate_note_hash_block_completion as blocks,transfer_relation as relation


def actual_ivk_call(selected):
    """Validate the selector's nested source call and its exact absorbed LCs.

    hash_rows.select retains the source observation under `call`, alongside
    checked parameters and round segments. Its first before-state contains the
    domain/arity tag and the three shared actual IVK input roles.
    """
    try:
        calls=selected['calls']
        if not isinstance(calls,list) or len(calls)!=1:
            raise relation.RelationError('actual native IVK single source call')
        selected_call=calls[0];call=selected_call['call'];parameters=selected_call['parameters'];graph=call['graph']
        identities=call['inputs'];observations=selected['observations']
        if (type(parameters['width']) is not int or parameters['width']!=6
                or any(type(graph[key]) is not int or graph[key]!=value
                       for key,value in (('domain',16),('arity',3),('width',6)))
                or call['role']!='authorization.ivk' or selected_call['role']!=call['role']
                or not isinstance(identities,list) or len(identities)!=3
                or any(not isinstance(identity,str) for identity in identities) or len(set(identities))!=3):
            raise relation.RelationError('actual native IVK width/domain/arity/source role')
        inputs=[observations[identity] for identity in identities]
        expected=[('linear',((1993,1),)),('linear',((1980,1),)),('linear',((1981,1),))]
        if inputs!=expected:
            raise relation.RelationError('actual native IVK exact observed input LC order')
        segments=selected_call['segments']
        if (not isinstance(segments,list) or not segments or segments[0]['index']!=0
                or segments[0]['before']!=[((0,3*256+16),),*(value for _,value in expected),(),()]):
            raise relation.RelationError('actual native IVK exact domain/arity absorbed state LC')
        return call
    except (KeyError,TypeError,IndexError) as error:
        raise relation.RelationError('actual native IVK nested source call shape') from error


def validate_selected(selected,metadata):
    """Exact derivative state recurrence against independently accepted params."""
    selected=copy.deepcopy(selected)
    call=selected['calls'][0];width=call['parameters']['width']
    if (type(width) is not int or width not in (3,6) or
            any(type(segment['index']) is not int for segment in call['segments']) or
            [segment['index'] for segment in call['segments']]!=list(range(65))):
        raise relation.RelationError('prefix hash exact65 width3/6 rounds')
    def lc(terms):
        if not isinstance(terms,(list,tuple)) or len(terms)>4096:
            raise relation.RelationError('prefix hash bounded derivative LC')
        result=[];previous=-1
        for term in terms:
            if not isinstance(term,(list,tuple)) or len(term)!=2:
                raise relation.RelationError('prefix hash derivative term shape')
            column=relation.natural(term[0],metadata['domain_size']);value=term[1]
            if column<=previous or type(value) is not int or not 0<value<relation.MODULUS:
                raise relation.RelationError('prefix hash canonical derivative term')
            previous=column;result.append((column,value))
        return tuple(result)
    for segment in call['segments']:
        for key in ('before','shifted','transformed','after'):
            if not isinstance(segment[key],(list,tuple)) or len(segment[key])!=width:
                raise relation.RelationError('prefix hash exact derivative state width')
            segment[key]=[lc(terms) for terms in segment[key]]
        for certificate in segment['fifths'].values():
            if certificate['kind']=='arithmetic':
                for key in ('square','fourth','auxiliary'):certificate[key]=lc(certificate[key])
        index=segment['index'];params=call['parameters']
        try:
            shifted=[blocks.rounds.canonical([*terms,(0,params['ark'][index][lane])])
                for lane,terms in enumerate(segment['before'])]
            expected_lanes=set(range(width)) if index<4 or index>=61 else {0}
            if set(segment['fifths'])!=expected_lanes:
                raise relation.RelationError('prefix exact nonlinear lane inventory')
            if segment['shifted']!=shifted:
                raise relation.RelationError('prefix actual round constant shift recurrence')
            for lane,certificate in segment['fifths'].items():
                if certificate['kind']=='constant':
                    base_lc=shifted[lane]
                    if any(column!=0 for column,_ in base_lc):
                        raise relation.RelationError('prefix folded lane has variable source')
                    coefficient=base_lc[0][1] if base_lc else 0
                    if (type(certificate['coefficient']) is not int or certificate['coefficient']!=coefficient or
                            segment['transformed'][lane]!=blocks.rounds.canonical([(0,pow(coefficient,5,relation.MODULUS))])):
                        raise relation.RelationError('prefix exact folded fifth recurrence')
            if any(segment['transformed'][lane]!=shifted[lane] for lane in set(range(width))-expected_lanes):
                raise relation.RelationError('prefix unchanged partial-round lanes')
            after=[blocks.rounds.canonical((column,value*coefficient) for terms,coefficient in
                zip(segment['transformed'],matrix_row) for column,value in terms) for matrix_row in params['mds']]
            if segment['after']!=after:
                raise relation.RelationError('prefix actual MDS recurrence')
        except (KeyError,TypeError,IndexError) as error:
            raise relation.RelationError('prefix typed round/parameter recurrence shape') from error
    if any(a['after']!=b['before'] for a,b in zip(call['segments'],call['segments'][1:])):
        raise relation.RelationError('prefix actual round-state adjacency')
    return selected


def _emit(selected,metadata,base,sound_module,sound_namespace,readonly_lcs,on_chunk=None):
    selected=validate_selected(selected,metadata)
    width=selected['calls'][0]['parameters']['width']
    context=(selected,dict(metadata=metadata),None)
    prior=[];support=set();owned=set();rows=set()
    for index,start in enumerate(range(0,65,5)):
        plan=blocks._chunk_plan(context,start,min(start+5,65),readonly_lcs=readonly_lcs)
        if set(plan['writes'])&(support|owned):
            raise relation.RelationError('prefix hash writes alter prior actual row support')
        support.update(c for row in plan['raw'].values() for lc in row for c,_ in lc)
        owned.update(plan['writes']);rows.update(plan['raw'])
        if on_chunk is not None:on_chunk(index,plan)
        module,source=blocks._chunk_source(base,index,plan,prior)
        yield module,source;prior.append(module)
    if rows!=set(selected['rows']):
        raise relation.RelationError('prefix hash exact captured row coverage')
    yield base+'Completion',blocks._composition(base,prior,metadata,rows_only=True,
        sound_module=sound_module,sound_namespace=sound_namespace,width=width)


def select_ivk(data,export,parameter_root,expected_relation,readonly_lcs):
    """Retained export must agree exactly with accepted real source/LC roles."""
    checked=ivk.inspect_metadata(data,parameter_root,expected_relation)
    metadata=checked['metadata'];names=checked['source_names']
    source={name:dict(node) for name,node in checked['source'].items()}
    for node in source.values():
        if node['kind']=='constant':node['value']=f"{node['value']:064x}"
    expressions=[dict(source=names[index],kind='linear',
        terms=[[c,f'{v:064x}'] for c,v in checked['derived'][index]]) for index in sorted(names)]
    expected_call=dict(role='authorization.ivk',domain=16,
        inputs=[names[index] for index in checked['handles'][:3]],
        output=names[checked['handles'][3]],source=source)
    same=lambda left,right:json.dumps(left,sort_keys=True,separators=(',',':'))==json.dumps(right,sort_keys=True,separators=(',',':'))
    if not isinstance(readonly_lcs,(list,tuple)) or len(readonly_lcs)>4096:
        raise relation.RelationError('bounded prefix readonly inventory')
    if (not isinstance(export,dict) or export.get('hash_scope')!='transfer-ivk-only'
            or export.get('relation_digest')!=expected_relation
            or export.get('domain_size')!=metadata['domain_size']
            or export.get('row_count')!=metadata['stored_rows']
            or not same(export.get('input_source_handles'),metadata['handles'][:3])
            or not same(export.get('expressions'),expressions) or not same(export.get('calls'),[expected_call])):
        raise relation.RelationError('prefix IVK export exact source/role/LC identity')
    selected=hash_rows.select(export,parameter_root)
    call=selected['calls'][0]
    call['segments']=[segment for segment in call['segments'] if segment['kind']=='round']
    if selected['outline']!=metadata['constant_copy']:
        raise relation.RelationError('prefix IVK exact constant copy')
    protected=[*readonly_lcs,*(checked['derived'][handle] for handle in checked['handles'][:3])]
    return validate_selected(selected,metadata),metadata,protected


def generate_ivk(data,export,parameter_root,expected_relation,readonly_lcs,*,on_chunk=None):
    selected,metadata,protected=select_ivk(data,export,parameter_root,expected_relation,readonly_lcs)
    yield from _emit(selected,metadata,'RuntimeTransferIvkHashOwned','RuntimeIvkHash_Data',
        'RuntimeHashBlock_authorization_ivk_0',protected,on_chunk)


def generate_rnk(data,extracted,block,parameter_root,expected_relation,ivk_handles,rnk_bindings,
                 readonly_lcs,*,on_chunk=None):
    """Later RNK blocks keep their checked physical recurrence boundary explicit."""
    if not isinstance(readonly_lcs,(list,tuple)) or len(readonly_lcs)>4096:
        raise relation.RelationError('bounded prefix readonly inventory')
    state=rnk.inspect_boundaries(data,expected_relation,ivk_handles,rnk_bindings)
    selected=rnk.row_permutation_selection(data,extracted,block,parameter_root,
        expected_relation,ivk_handles,rnk_bindings)
    # Initial absorbed-state LCs are reads, including the earlier permutation
    # output for block1. Protect those actual roles, not desired hash values.
    protected=[*readonly_lcs,*selected['calls'][0]['segments'][0]['before']]
    yield from _emit(selected,state['metadata'],f'RuntimeTransferRnkHash{block}Owned',
        f'RuntimeRnkHash{block}_Data',f'RuntimeHashBlock_authorization_rnk_permutation{block}_0',
        protected,on_chunk)
