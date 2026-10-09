"""Qualified56page ingress, retaining pending page bytes and exact source checks."""
import json
from blake3 import blake3
from . import transfer_note_hash_pages as hashes, transfer_note_tree as tree
from . import transfer_relation as relation

SCOPE='55 hash pages plus one two-spend/48-tree LC page from one lowering; native/kernel joins open'


def encoded(obj):return (json.dumps(obj,separators=(',',':'))+'\n').encode()


def inspect_manifest(data,expected_relation):
    if not isinstance(data,bytes) or len(data)>128*1024:
        raise relation.RelationError('combined note manifest byte bound')
    obj=relation.record(data)
    if (obj.get('schema'),obj.get('scope'))!=('shieldd-transfer-note-t4-pages-v1',SCOPE):
        raise relation.RelationError('combined note manifest schema/scope')
    pages=obj.get('pages')
    if not isinstance(pages,list) or len(pages)!=56:
        raise relation.RelationError('combined note exact56 page inventory')
    view=dict(obj,schema='shieldd-transfer-note-hash-pages-v1',scope=hashes.SCOPE,pages=pages[:55])
    hashes.inspect_manifest(encoded(view),expected_relation)
    last=pages[55]
    if (not isinstance(last,dict) or set(last)!={'ordinal','slot','role','level','block','blake3'} or
        any(type(last[k]) is not int for k in ('ordinal','slot','level','block')) or
        (last['ordinal'],last['slot'],last['role'],last['level'],last['block'])!=(55,0,'tree',0,0) or
        not isinstance(last['blake3'],str) or len(last['blake3'])!=64 or
        any(c not in '0123456789abcdef' for c in last['blake3'])):
        raise relation.RelationError('combined note tree descriptor/order')
    return obj


def qualified_tree(manifest_data,page_data,accepted_roles):
    manifest=inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    if not isinstance(page_data,bytes) or len(page_data)>4*1024*1024:
        raise relation.RelationError('combined tree page byte bound')
    if blake3(page_data).hexdigest()!=manifest['pages'][55]['blake3']:
        raise relation.RelationError('combined tree page bytes/digest mismatch')
    obj=relation.record(page_data)
    for part in (obj,obj.get('spend')):
        if (not isinstance(part,dict) or part.get('ordinary_full_ordered_rows_equal') is not False or
            part.get('repeated_observations_equal') is not False or
            any(part.get(k)!=manifest[k] for k in ('relation_digest','domain_size','full_rows','constant_copy'))):
            raise relation.RelationError('combined tree/spend page pending identity mismatch')
    spend=dict(obj['spend'],ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
    view=dict(obj,spend=spend,ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
    data,note_data=encoded(view),encoded(spend)
    tree.inspect_metadata(data,note_data,accepted_roles)
    return data,note_data


def qualified_hash(manifest_data,page_data,ordinal,tree_data,note_data,accepted_roles):
    manifest=inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    view=dict(manifest,schema='shieldd-transfer-note-hash-pages-v1',scope=hashes.SCOPE,pages=manifest['pages'][:55])
    result=hashes.qualified_page(encoded(view),page_data,ordinal,note_data,accepted_roles)
    if relation.record(result)['role']=='state':
        tree.inspect_hash_link(tree_data,result,note_data,accepted_roles)
    return result
