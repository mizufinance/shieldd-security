"""Actual ASSET_GENERATOR26/1 ingress closes the accepted map's hash/u root.

Field/source/ordinary-row correspondence only; cryptographic hash assumptions,
map codec and full Transfer constructive composition remain separate.
"""
import hashlib,re
from . import transfer_asset_map as maps,transfer_note_hash as hashes,transfer_relation as relation
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical,combine,source_index
from .generate_hash_round import generate_selected_block,split_block_modules

SCOPE='balance ASSET_GENERATOR26/1 permutation with exact asset/map-u LCs; native/kernel joins open'


def inspect_boundaries(data,map_data,accepted_roles):
    accepted=maps.inspect_metadata(map_data,accepted_roles)
    if not isinstance(data,bytes) or len(data)>4*1024*1024:raise relation.RelationError('asset hash page byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','slot','role','level','block',
        'map_input','hash','expressions','nodes'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=(
            'shieldd-transfer-asset-hash-block-v1','transfer',SCOPE):raise relation.RelationError('asset hash closed schema/scope')
    if any(obj[key]!=accepted['metadata'][key] for key in ('relation_digest','domain_size','full_rows','constant_copy')) or (
            obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('asset hash map/full relation identity/pending mismatch')
    if any(type(obj[key]) is not int or obj[key]!=0 for key in ('slot','level','block')) or obj['role']!='asset':
        raise relation.RelationError('asset hash exact balance role')
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],4096,'asset hash')
    if sum(map(len,observed.values()))>65536:raise relation.RelationError('asset hash LC term bound')
    required=set()
    def value(ref):
        if not isinstance(ref,dict) or len(ref)!=1:raise relation.RelationError('asset hash reference shape')
        if set(ref)=={'source'}:
            handle=source_index(ref['source']);required.add(handle)
            if handle not in observed:raise relation.RelationError('asset hash missing source LC')
            return observed[handle]
        if set(ref)=={'native'}:
            encoded=ref['native']
            if not isinstance(encoded,str) or not re.fullmatch('[0-9a-f]{64}',encoded) or int(encoded,16)>=relation.MODULUS:
                raise relation.RelationError('asset hash noncanonical native reference')
            return canonical([(0,int(encoded,16))])
        raise relation.RelationError('asset hash unknown reference')
    call=obj['hash'];map_meta=accepted['metadata']
    if (not isinstance(call,dict) or set(call)!={'domain','inputs','output','blocks'} or
        type(call['domain']) is not int or call['domain']!=26 or call['inputs']!=[map_meta['asset']] or
        call['output']!=map_meta['hash'] or obj['map_input']!=map_meta['values'][0] or
        obj['map_input']!=call['output'] or not isinstance(call['blocks'],list) or len(call['blocks'])!=1):
        raise relation.RelationError('asset hash exact domain/arity/asset/map-u source links')
    for ref in [map_meta['asset'],map_meta['hash'],map_meta['values'][0]]:
        handle=source_index(ref['source'])
        if value(ref)!=accepted['observed'][handle]:raise relation.RelationError('asset hash accepted map ingress LC mismatch')
    part=call['blocks'][0]
    if not isinstance(part,dict) or set(part)!={'before','after'} or any(
            not isinstance(part[key],list) or len(part[key])!=3 for key in ('before','after')):
        raise relation.RelationError('asset hash one full width3 checkpoint')
    expected=[canonical([(0,282)]),value(call['inputs'][0]),()]
    before=[value(ref) for ref in part['before']];after=[value(ref) for ref in part['after']]
    if before!=expected or call['output']!=part['after'][1] or value(call['output'])!=after[1]:
        raise relation.RelationError('asset hash native IV/absorption/final lane mismatch')
    return dict(metadata=obj,observed=observed,boundary_sources=required,block=0,
        metadata_sha256=hashlib.sha256(data).hexdigest())


def inspect_metadata(data,map_data,accepted_roles,parameter_root):
    return hashes._inspect_permutation(inspect_boundaries(data,map_data,accepted_roles),parameter_root,width=3)


def extract(data,stream,map_data,accepted_roles,parameter_root):
    return hashes._extract_permutation(inspect_metadata(data,map_data,accepted_roles,parameter_root),stream,label='asset-hash')


def round_selection(data,extracted,map_data,accepted_roles,parameter_root):
    return hashes._select_permutation(inspect_metadata(data,map_data,accepted_roles,parameter_root),extracted,parameter_root,role_prefix='balance')


def generate_permutation(data,extracted,map_data,accepted_roles,parameter_root,namespace='RuntimeTransferAssetHash'):
    checked=inspect_metadata(data,map_data,accepted_roles,parameter_root)
    selected=hashes._select_permutation(checked,extracted,parameter_root,role_prefix='balance')
    source=generate_selected_block(checked['metadata'],selected,selected['calls'][0]['role'],0,
        checked['metadata_sha256'],permutation_only=True)
    return split_block_modules(source,namespace,5)
