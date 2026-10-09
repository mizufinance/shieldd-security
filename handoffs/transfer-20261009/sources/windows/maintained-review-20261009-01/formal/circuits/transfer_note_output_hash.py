"""Actual output NOTE15/8 and recovery20/7 native/source/row ingress.

Accept the two-output roles first. Both six-lane permutations and their exact
absorption LCs are mandatory. A computed recovery hash and supplied capsule
commitment remain distinct until the ordinary assertion row is checked.
"""
import hashlib
from . import transfer_note_outputs as outputs,transfer_note_hash as hashes
from . import transfer_relation as relation,transfer_arithmetic as arithmetic,transfer_note_hash_join as joins
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical,combine,source_index
from .generate_hash_round import generate_selected_block,split_block_modules

SCOPE='one output NOTE15/8 or recovery20/7 permutation and exact two-output source roles; native/kernel joins open'


def inspect_boundaries(data,output_data,accepted_roles):
    accepted=outputs.inspect_metadata(output_data,accepted_roles)
    if not isinstance(data,bytes) or len(data)>4*1024*1024:
        raise relation.RelationError('output hash page byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','slot','role','level','block',
        'hash','supplied_commitment','expressions','nodes'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=('shieldd-transfer-note-output-hash-block-v1','transfer',SCOPE):
        raise relation.RelationError('output hash closed schema/scope')
    if (any(obj[k]!=accepted['metadata'][k] for k in ('relation_digest','domain_size','full_rows','constant_copy')) or
        obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('output hash full relation identity/pending mismatch')
    slot=relation.natural(obj['slot'],2);block=relation.natural(obj['block'],2)
    if type(obj['level']) is not int or obj['level']!=0 or obj['role'] not in ('note','recovery'):
        raise relation.RelationError('output hash exact native role/level')
    role=obj['role'];domain,arity=(15,8) if role=='note' else (20,7)
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],4096,'output hash')
    for handle,lc in accepted['observed'].items():
        if observed.get(handle)!=lc:raise relation.RelationError('output hash two-output source LC mismatch')
    required=set(accepted['observed'])
    def value(ref):
        if not isinstance(ref,dict) or len(ref)!=1:raise relation.RelationError('output hash reference shape')
        if set(ref)=={'source'}:
            handle=source_index(ref['source']);required.add(handle)
            if handle not in observed:raise relation.RelationError('output hash missing source LC')
            return observed[handle]
        if set(ref)=={'native'}:
            encoded=ref['native']
            if not isinstance(encoded,str) or len(encoded)!=64 or any(c not in '0123456789abcdef' for c in encoded) or int(encoded,16)>=relation.MODULUS:
                raise relation.RelationError('output hash native encoding')
            return canonical([(0,int(encoded,16))])
        raise relation.RelationError('output hash unknown reference')
    call=obj['hash'];output=accepted['metadata']['outputs'][slot]
    wanted=output['note'] if role=='note' else output['capsule']
    supplied=output['commitment'] if role=='note' else output['capsule_commitment']
    if (not isinstance(call,dict) or set(call)!={'domain','inputs','output','blocks'} or
        type(call['domain']) is not int or call['domain']!=domain or call['inputs']!=wanted or
        not isinstance(call['inputs'],list) or len(call['inputs'])!=arity or
        not isinstance(call['blocks'],list) or len(call['blocks'])!=2 or obj['supplied_commitment']!=supplied):
        raise relation.RelationError('output hash exact domain/arity/source/supplied commitment')
    if role=='note' and call['output']!=output['computed_commitment']:
        raise relation.RelationError('output NOTE computed source mismatch')
    inputs=[value(ref) for ref in call['inputs']];result=value(call['output']);value(supplied)
    state=[canonical([(0,256*arity+domain)]),(),(),(),(),()]
    for ordinal,part in enumerate(call['blocks']):
        if not isinstance(part,dict) or set(part)!={'before','after'} or any(
                not isinstance(part[key],list) or len(part[key])!=6 for key in ('before','after')):
            raise relation.RelationError('output hash two blocks six-lane shape')
        before=[value(ref) for ref in part['before']];after=[value(ref) for ref in part['after']]
        expected=list(state)
        for lane,item in enumerate(inputs[5*ordinal:5*(ordinal+1)],1):expected[lane]=combine(expected[lane],item)
        if before!=expected:raise relation.RelationError('output hash exact adjacent absorption LC mismatch')
        state=after
    if result!=state[1] or call['output']!=call['blocks'][-1]['after'][1]:
        raise relation.RelationError('output hash exact final source lane')
    return dict(metadata=obj,observed=observed,boundary_sources=required,block=block,
        metadata_sha256=hashlib.sha256(data).hexdigest())


def inspect_metadata(data,output_data,accepted_roles,parameter_root):
    return hashes._inspect_permutation(inspect_boundaries(data,output_data,accepted_roles),parameter_root)


def extract(data,stream,output_data,accepted_roles,parameter_root):
    checked=inspect_metadata(data,output_data,accepted_roles,parameter_root)
    result=hashes._extract_permutation(checked,stream,label='output-hash')
    result['scope']='actual output permutation rows; supplied commitment assertion/native joins separate'
    return result


def round_selection(data,extracted,output_data,accepted_roles,parameter_root):
    checked=inspect_metadata(data,output_data,accepted_roles,parameter_root)
    return hashes._select_permutation(checked,extracted,parameter_root,role_prefix='output')


def extract_binding(data,stream,output_data,accepted_roles):
    checked=inspect_boundaries(data,output_data,accepted_roles);obj=checked['metadata']
    observed=checked['observed'];computed=observed[source_index(obj['hash']['output']['source'])]
    supplied=observed[source_index(obj['supplied_commitment']['source'])]
    copy=obj['constant_copy'];delta=combine(computed,supplied,-1)
    outline=lambda terms:canonical((copy if c==0 else c,v) for c,v in terms)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy'],(outline(delta),()):['computed-supplied-binding']}
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,[],[],label='output-hash-binding')
    result.update(metadata_sha256=checked['metadata_sha256'],slot=obj['slot'],role=obj['role'],block=obj['block'],
        scope='actual computed-to-supplied output hash assertion only')
    return result


def generate_permutation(data,extracted,output_data,accepted_roles,parameter_root):
    checked=inspect_metadata(data,output_data,accepted_roles,parameter_root)
    selected=hashes._select_permutation(checked,extracted,parameter_root,role_prefix='output')
    obj=checked['metadata'];role=selected['calls'][0]['role']
    source=generate_selected_block(obj,selected,role,0,checked['metadata_sha256'],permutation_only=True)
    name=f'RuntimeTransferOutput{obj["slot"]}{obj["role"].capitalize()}HashBlock{obj["block"]}'
    return split_block_modules(source,name,5)


def inspect_calls(page_data,output_data,accepted_roles):
    if not isinstance(page_data,(tuple,list)) or len(page_data)!=2:
        raise relation.RelationError('output complete call requires exact two blocks')
    checked=[inspect_boundaries(data,output_data,accepted_roles) for data in page_data]
    first=checked[0]['metadata'];shared={}
    if [part['metadata']['block'] for part in checked]!=[0,1]:
        raise relation.RelationError('output complete call reordered/missing blocks')
    for part in checked:
        obj=part['metadata']
        if any(obj[key]!=first[key] for key in ('relation_digest','domain_size','full_rows','constant_copy','slot','role','level','supplied_commitment','hash')):
            raise relation.RelationError('output complete call native/source constructor mismatch')
        for handle,terms in part['observed'].items():
            if handle in shared and shared[handle]!=terms:raise relation.RelationError('output complete call shared LC mismatch')
            shared[handle]=terms
    return checked


def generate_call(page_data,extractions,output_data,accepted_roles,parameter_root):
    checked=inspect_calls(page_data,output_data,accepted_roles)
    if not isinstance(extractions,(tuple,list)) or len(extractions)!=2:
        raise relation.RelationError('output complete call row extraction inventory')
    selected=[round_selection(data,extracted,output_data,accepted_roles,parameter_root)
        for data,extracted in zip(page_data,extractions)]
    obj=checked[0]['metadata'];base=f'RuntimeTransferOutput{obj["slot"]}{obj["role"].capitalize()}Hash'
    return joins._generate_checked(checked,selected,base)
