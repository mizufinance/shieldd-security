"""Exact recovery secret11/2, confirmation21/4 and stream10/2 hash ingress.

Each page carries one bounded full permutation cone. Recovery metadata and
native source roles are mandatory; hash identity alone does not join semantics.
"""
import hashlib,re
from . import transfer_recovery_capsule as capsules,transfer_note_hash as hashes,transfer_relation as relation
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical,source_index
from .generate_hash_round import generate_selected_block,split_block_modules

SCOPE='one recovery secret11/2 confirmation21/4 or stream10/2 permutation with exact two capsule source roles; native/kernel joins open'
ROLES=('secret','confirmation','amount-stream','blinding-stream')


def inspect_boundaries(data,recovery_data,output_data,accepted_roles):
    accepted=capsules.inspect_metadata(recovery_data,output_data,accepted_roles)
    if not isinstance(data,bytes) or len(data)>4*1024*1024:raise relation.RelationError('recovery hash page byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
          'ordinary_full_ordered_rows_equal','repeated_observations_equal','slot','role','level','block','hash','expressions','nodes'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=(
            'shieldd-transfer-recovery-hash-block-v1','transfer',SCOPE):raise relation.RelationError('recovery hash closed schema/scope')
    if any(obj[k]!=accepted['metadata'][k] for k in ('relation_digest','domain_size','full_rows','constant_copy')) or (
            obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('recovery hash accepted relation identity/pending mismatch')
    slot=relation.natural(obj['slot'],2);role=obj['role']
    if role not in ROLES or any(type(obj[k]) is not int or obj[k]!=0 for k in ('level','block')):
        raise relation.RelationError('recovery hash exact role/level/block')
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],4096,'recovery hash')
    if sum(map(len,observed.values()))>65536:raise relation.RelationError('recovery hash LC term bound')
    required=set(accepted['observed'])
    for handle,lc in accepted['observed'].items():
        if observed.get(handle)!=lc:raise relation.RelationError('recovery hash accepted source LC mismatch')
    def value(ref):
        if not isinstance(ref,dict) or len(ref)!=1:raise relation.RelationError('recovery hash reference shape')
        if set(ref)=={'source'}:
            handle=source_index(ref['source']);required.add(handle)
            if handle not in observed:raise relation.RelationError('recovery hash missing source LC')
            return observed[handle]
        if set(ref)=={'native'}:
            encoded=ref['native']
            if not isinstance(encoded,str) or not re.fullmatch('[0-9a-f]{64}',encoded) or int(encoded,16)>=relation.MODULUS:
                raise relation.RelationError('recovery hash noncanonical native reference')
            return canonical([(0,int(encoded,16))])
        raise relation.RelationError('recovery hash unknown reference')
    entry=accepted['metadata']['capsules'][slot]
    if role=='secret':domain,width,wanted,result=11,3,entry['shared'],entry['secret']
    elif role=='confirmation':domain,width,wanted,result=21,6,[entry['seed'],*entry['capsule'][:2],entry['capsule'][3]],entry['computed_confirmation']
    else:
        counter=int(role=='blinding-stream');domain,width=10,3
        wanted=[entry['seed'],{'native':f'{counter:064x}'}]
        result=entry['blinding_stream' if counter else 'amount_stream']
    call=obj['hash']
    if not isinstance(call,dict) or set(call)!={'domain','inputs','output','blocks'} or (
            type(call['domain']) is not int or call['domain']!=domain or call['inputs']!=wanted or call['output']!=result or
            not isinstance(call['blocks'],list) or len(call['blocks'])!=1):
        raise relation.RelationError('recovery hash exact native domain/arity/source output')
    part=call['blocks'][0]
    if not isinstance(part,dict) or set(part)!={'before','after'} or any(
            not isinstance(part[k],list) or len(part[k])!=width for k in ('before','after')):
        raise relation.RelationError('recovery hash one full native width checkpoint')
    expected=[canonical([(0,domain+256*len(wanted))]),*[value(ref) for ref in wanted]]
    expected.extend([()]*(width-len(expected)))
    before=[value(ref) for ref in part['before']];after=[value(ref) for ref in part['after']]
    if before!=expected or value(result)!=after[1] or result!=part['after'][1]:
        raise relation.RelationError('recovery hash IV/absorption/final lane mismatch')
    return dict(metadata=obj,observed=observed,boundary_sources=required,block=0,width=width,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def inspect_metadata(data,recovery_data,output_data,accepted_roles,parameter_root):
    checked=inspect_boundaries(data,recovery_data,output_data,accepted_roles)
    return hashes._inspect_permutation(checked,parameter_root,width=checked['width'])


def extract(data,stream,recovery_data,output_data,accepted_roles,parameter_root):
    return hashes._extract_permutation(inspect_metadata(data,recovery_data,output_data,accepted_roles,parameter_root),
                                       stream,label='recovery-hash')


def round_selection(data,extracted,recovery_data,output_data,accepted_roles,parameter_root):
    checked=inspect_metadata(data,recovery_data,output_data,accepted_roles,parameter_root)
    return hashes._select_permutation(checked,extracted,parameter_root,role_prefix='recovery')


def generate_permutation(data,extracted,recovery_data,output_data,accepted_roles,parameter_root):
    checked=inspect_metadata(data,recovery_data,output_data,accepted_roles,parameter_root)
    selected=hashes._select_permutation(checked,extracted,parameter_root,role_prefix='recovery')
    obj=checked['metadata'];name=f'RuntimeTransferRecovery{obj["slot"]}{obj["role"].title().replace("-","")}Hash'
    source=generate_selected_block(obj,selected,selected['calls'][0]['role'],0,checked['metadata_sha256'],permutation_only=True)
    return split_block_modules(source,name,5)
