"""Closed caller/spend boundary ingress; no inferred DAG or native semantics."""
import hashlib
import re
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, source_index

SCOPE = 'existing caller/spend authorization boundaries and LCs only; source/row/native semantic joins open'
P = relation.MODULUS


def _expressions(values, domain, constant_copy, limit, label):
    """Validate captured pre-outline LCs before using any shared selection."""
    if not isinstance(values, list) or not 1 <= len(values) <= limit:
        raise relation.RelationError(label + ' expression selection bound')
    observed = {}
    previous = None
    for item in values:
        if not isinstance(item, dict) or set(item) != {'source', 'terms'}:
            raise relation.RelationError('malformed ' + label + ' expression')
        index = source_index(item['source'])
        if previous is not None and index <= previous:
            raise relation.RelationError(label + ' expression selections unordered/duplicate')
        previous = index
        relation.terms(item['terms'], domain)
        terms = tuple((column, int(value, 16)) for column, value in item['terms'])
        if canonical(terms) != terms or any(column == constant_copy for column, _ in terms):
            raise relation.RelationError(label + ' expression canonical/outline mismatch')
        if index[0] == 1 and terms != ((3 + index[1], 1),):
            raise relation.RelationError(label + ' witness/column mismatch')
        if index[0] == 0 and any(column != 0 for column, _ in terms):
            raise relation.RelationError(label + ' constant projection mismatch')
        observed[index] = terms
    return observed


def inspect_metadata(data, expected_relation, expected_ivk_handles, expected_rnk, expected_ivk=None):
    """Join role metadata to already accepted RNK-DH and IVK captures.

    Callers must supply the accepted capture metadata, not just a digest. This
    checks relation shape, role identity and shared LCs; it neither accepts those
    captures on its own nor establishes runtime, DAG, row or native semantics.
    """
    if not isinstance(data,bytes) or len(data) > 2*1024*1024:
        raise relation.RelationError('authorization role metadata size bound')
    if not isinstance(expected_relation,str) or not re.fullmatch('[0-9a-f]{64}',expected_relation):
        raise relation.RelationError('exact authorization role relation required')
    if not isinstance(expected_ivk_handles,(list,tuple)) or len(expected_ivk_handles) != 4:
        raise relation.RelationError('wrong accepted authorization IVK handles')
    ivk=tuple(source_index(h) for h in expected_ivk_handles)
    if len(set(ivk)) != 4 or any(tag == 0 for tag, _ in ivk):
        raise relation.RelationError('aliased/native accepted authorization IVK handles')
    if not isinstance(expected_rnk,dict) or not isinstance(expected_rnk.get('rnk_bindings'),dict):
        raise relation.RelationError('accepted RNK role metadata required')
    if not isinstance(expected_ivk,dict):
        raise relation.RelationError('accepted IVK role metadata required')
    try:
        obj=relation.record(data)
    except RecursionError as error:
        raise relation.RelationError('authorization role JSON nesting bound') from error
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
          'ordinary_full_ordered_rows_equal','ivk_handles','caller','spend','rnk_bindings','expressions'}
    if set(obj) != keys or obj['schema'] != 'shieldd-transfer-authorization-roles-v1' or obj['family'] != 'transfer' or obj['scope'] != SCOPE:
        raise relation.RelationError('authorization role schema/scope mismatch')
    if obj['relation_digest'] != expected_relation or obj['ordinary_full_ordered_rows_equal'] is not True:
        raise relation.RelationError('authorization role ordinary identity mismatch')
    domain=relation.natural(obj['domain_size']); count=relation.natural(obj['full_rows'])
    copy=relation.natural(obj['constant_copy'],domain)
    if domain < 4 or domain & (domain-1) or not 0 < count <= domain or copy < 3:
        raise relation.RelationError('authorization role relation shape mismatch')
    accepted_maps = []
    for accepted, label, row_key, handles_key in (
            (expected_rnk, 'RNK', 'full_rows', 'ivk_handles'),
            (expected_ivk, 'IVK', 'stored_rows', 'handles')):
        if (accepted.get('relation_digest') != expected_relation or
                relation.natural(accepted.get('domain_size')) != domain or
                relation.natural(accepted.get(row_key)) != count or
                relation.natural(accepted.get('constant_copy'), domain) != copy):
            raise relation.RelationError('authorization/accepted ' + label + ' relation shape mismatch')
        handles = accepted.get(handles_key)
        if (not isinstance(handles, list) or len(handles) != 4 or
                tuple(source_index(handle) for handle in handles) != ivk):
            raise relation.RelationError('authorization/accepted ' + label + ' IVK role mismatch')
        if label == 'IVK' and accepted.get('ordinary_full_ordered_rows_equal') is not True:
            raise relation.RelationError('authorization/accepted IVK ordinary identity mismatch')
        accepted_maps.append(_expressions(accepted.get('expressions'), domain, copy, 4096,
                                         'accepted ' + label))
    if not isinstance(obj['ivk_handles'],list) or len(obj['ivk_handles']) != 4 or tuple(source_index(h) for h in obj['ivk_handles']) != ivk:
        raise relation.RelationError('authorization/accepted IVK role mismatch')
    required=set(ivk)
    def ref(value, native=False):
        if not isinstance(value,dict) or len(value) != 1:
            raise relation.RelationError('malformed authorization role reference')
        if native:
            coefficient=value.get('native')
            if not isinstance(coefficient,str) or not re.fullmatch('[0-9a-f]{64}',coefficient) or int(coefficient,16) >= P:
                raise relation.RelationError('noncanonical native authorization role')
            return
        if set(value) != {'source'}:
            raise relation.RelationError('authorization role must be Source')
        required.add(source_index(value['source']))
    def array(value,size,native=False):
        if not isinstance(value,list) or len(value) != size:
            raise relation.RelationError('wrong authorization role array shape')
        for x in value:ref(x,native)
    caller,spend=obj['caller'],obj['spend']
    caller_keys={'regulated','asset','leaf_ring','fixed_ring','selected_ring','address','rnk_dh','registered_rnk','ak','nk','effective_nk'}
    spend_keys={'ak','randomizer','bits','generator','contribution','computed','rk'}
    if not isinstance(caller,dict) or set(caller) != caller_keys or not isinstance(spend,dict) or set(spend) != spend_keys:
        raise relation.RelationError('authorization caller/spend closed shape mismatch')
    for key in ('regulated','asset','registered_rnk','nk','effective_nk'):ref(caller[key])
    for key in ('leaf_ring','selected_ring','rnk_dh','ak'):array(caller[key],2)
    array(caller['fixed_ring'],2,True);array(caller['address'],4)
    for key in ('ak','contribution','computed','rk'):array(spend[key],2)
    array(spend['generator'],2,True);ref(spend['randomizer'])
    bits=spend['bits']
    if not isinstance(bits,list) or len(bits) != 252:
        raise relation.RelationError('authorization randomizer bit length mismatch')
    bit_handles=tuple(source_index(x) for x in bits)
    if len(set(bit_handles)) != 252 or any(tag != 1 for tag,_ in bit_handles):
        raise relation.RelationError('authorization randomizer bits must be distinct witnesses')
    required.update(bit_handles)
    rnk=obj['rnk_bindings']
    if not isinstance(rnk,dict) or set(rnk) != {'inputs','hash','commitment','regulated','registered','effective_nk'}:
        raise relation.RelationError('authorization RNK bindings closed shape mismatch')
    array(rnk['inputs'],9)
    for key in ('hash','commitment','regulated','registered','effective_nk'):ref(rnk[key])
    accepted_bindings = expected_rnk['rnk_bindings']
    if set(accepted_bindings) != set(rnk):
        raise relation.RelationError('accepted RNK bindings closed shape mismatch')
    array(accepted_bindings['inputs'],9)
    for key in ('hash','commitment','regulated','registered','effective_nk'):
        ref(accepted_bindings[key])
    array(expected_rnk.get('base'),2)
    if rnk != expected_rnk['rnk_bindings']:
        raise relation.RelationError('authorization/accepted RNK bindings mismatch')
    if (caller['address'] != rnk['inputs'][2:6] or caller['asset'] != rnk['inputs'][6] or
            caller['selected_ring'] != rnk['inputs'][7:9] or caller['rnk_dh'] != expected_rnk.get('base') or
            caller['regulated'] != rnk['regulated'] or caller['registered_rnk'] != rnk['registered'] or
            caller['effective_nk'] != rnk['effective_nk']):
        raise relation.RelationError('authorization caller/RNK source role mismatch')
    if (source_index(caller['nk']['source']) != ivk[0] or
            tuple(source_index(x['source']) for x in caller['ak']) != ivk[1:3] or spend['ak'] != caller['ak']):
        raise relation.RelationError('authorization caller/spend/IVK AK or NK mismatch')
    rnk_required = {source_index(value['source']) for value in caller['rnk_dh'] + rnk['inputs'][:2]}
    if not rnk_required <= set(accepted_maps[0]):
        raise relation.RelationError('accepted RNK authorization role expression coverage mismatch')
    if not set(ivk) <= set(accepted_maps[1]):
        raise relation.RelationError('accepted IVK authorization role expression coverage mismatch')
    observed = _expressions(obj['expressions'], domain, copy, 512, 'authorization')
    if set(observed) != required:
        raise relation.RelationError('authorization boundary expression coverage mismatch')
    shared = dict(observed)
    for accepted in accepted_maps:
        for index, terms in accepted.items():
            if index in shared and shared[index] != terms:
                raise relation.RelationError('authorization/accepted shared source LC mismatch')
            shared[index] = terms
    return dict(metadata=obj,observed=observed,bit_handles=bit_handles,
                metadata_sha256=hashlib.sha256(data).hexdigest(),
                scope='closed actual caller/spend boundaries only; row/native interpretation joins separate')
