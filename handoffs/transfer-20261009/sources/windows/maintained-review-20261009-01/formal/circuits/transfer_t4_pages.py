"""Strict65 bounded ingress; only qualified manifest views inherit parity.

Page identity binds the original pending bytes. Existing typed source/native
checks and original-row extraction remain required for every component.
"""
import hashlib
from blake3 import blake3
from . import transfer_relation as relation,transfer_note_hash_pages as prefix
from . import transfer_note_tree as tree,transfer_note_spend as spend,transfer_note_outputs as outputs
from . import transfer_note_output_hash as output_hash,transfer_asset_hash as asset_hash
from .transfer_note_t4_pages import encoded

SCOPE='55 input hash +8 output hash +1 asset hash +1 compact roles page from one lowering; native/kernel joins open'
IDENTITY=('relation_digest','domain_size','full_rows','constant_copy')
FLAGS=('ordinary_full_ordered_rows_equal','repeated_observations_equal')


def inventory():
    return prefix.inventory()+[(slot,role,0,block) for slot in range(2) for role in ('note','recovery') for block in range(2)]+[(0,'asset',0,0),(0,'roles',0,0)]


def inspect_manifest(data,expected_relation):
    if not isinstance(data,bytes) or len(data)>128*1024:raise relation.RelationError('T4 manifest byte bound')
    obj=relation.record(data)
    if not isinstance(obj,dict) or (obj.get('schema'),obj.get('scope'))!=('shieldd-transfer-t4-pages-v1',SCOPE):
        raise relation.RelationError('T4 manifest schema/scope')
    pages=obj.get('pages')
    if not isinstance(pages,list) or len(pages)!=65:raise relation.RelationError('T4 exact65 inventory')
    first=dict(obj,schema='shieldd-transfer-note-hash-pages-v1',scope=prefix.SCOPE,pages=pages[:55])
    prefix.inspect_manifest(encoded(first),expected_relation)
    for ordinal,(descriptor,wanted) in enumerate(zip(pages,inventory())):
        if not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','slot','role','level','block','blake3'}:
            raise relation.RelationError('T4 closed descriptor')
        if any(type(descriptor[k]) is not int for k in ('ordinal','slot','level','block')) or (descriptor['ordinal'],descriptor['slot'],descriptor['role'],descriptor['level'],descriptor['block'])!=(ordinal,*wanted):
            raise relation.RelationError('T4 exact native descriptor order')
        digest=descriptor['blake3']
        if not isinstance(digest,str) or len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):
            raise relation.RelationError('T4 digest encoding')
    return obj


def inspect_component_manifest(data,expected_relation):
    """Accept the original qualified65 or qualified74 parent, without relabeling.

The latter's complete inventory/prefix has already been validated by its own
adapter. Component functions read the original descriptors and flags directly.
"""
    if not isinstance(data,bytes) or len(data)>128*1024:raise relation.RelationError('T4 component manifest byte bound')
    obj=relation.record(data)
    if isinstance(obj,dict) and obj.get('schema')=='shieldd-transfer-t4-recovery-pages-v1':
        from . import transfer_recovery_pages
        return transfer_recovery_pages.inspect_manifest(data,expected_relation)
    return inspect_manifest(data,expected_relation)


def pending_page(manifest,page_data,ordinal,*,role_fields=True):
    """Checks a page under an already validated manifest; never changes bytes."""
    ordinal=relation.natural(ordinal,len(manifest['pages']))
    if not isinstance(page_data,bytes) or len(page_data)>4*1024*1024:raise relation.RelationError('T4 page byte bound')
    descriptor=manifest['pages'][ordinal]
    if blake3(page_data).hexdigest()!=descriptor['blake3']:raise relation.RelationError('T4 original page bytes/digest mismatch')
    obj=relation.record(page_data)
    if not isinstance(obj,dict) or any(obj.get(k) is not False for k in FLAGS) or any(obj.get(k)!=manifest[k] for k in IDENTITY):
        raise relation.RelationError('T4 page pending/full relation identity')
    if role_fields and any(obj.get(k)!=descriptor[k] or k!='role' and type(obj.get(k)) is not int for k in ('slot','role','level','block')):
        raise relation.RelationError('T4 page exact native role')
    return obj


def qualified_part(obj,manifest):
    if not isinstance(obj,dict) or any(obj.get(k) is not False for k in FLAGS) or any(obj.get(k)!=manifest[k] for k in IDENTITY):
        raise relation.RelationError('T4 nested pending/full relation identity')
    return dict(obj,ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)


def qualified_roles(manifest_data,page_data,accepted_roles):
    manifest=inspect_component_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    obj=pending_page(manifest,page_data,64,role_fields=False)
    keys={'schema','family','scope','tree','outputs',*IDENTITY,*FLAGS}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=('shieldd-transfer-t4-roles-v1','transfer','two spend/output roles and 48 tree levels; actual row/native joins open'):
        raise relation.RelationError('T4 compact roles closed schema/scope')
    tree_obj=qualified_part(obj['tree'],manifest)
    note_obj=qualified_part(tree_obj['spend'],manifest)
    tree_obj['spend']=note_obj
    output_obj=qualified_part(obj['outputs'],manifest)
    tree_data,note_data,output_data=encoded(tree_obj),encoded(note_obj),encoded(output_obj)
    note_checked=spend.inspect_metadata(note_data,accepted_roles)
    tree_checked=tree.inspect_metadata(tree_data,note_data,accepted_roles)
    output_checked=outputs.inspect_metadata(output_data,accepted_roles)
    shared={}
    for owner in (note_checked,tree_checked,output_checked):
        for handle,lc in owner['observed'].items():
            if handle in shared and shared[handle]!=lc:raise relation.RelationError('T4 compact roles shared LC drift')
            shared[handle]=lc
    return dict(tree_data=tree_data,note_data=note_data,output_data=output_data,
                original_pending_sha256=hashlib.sha256(page_data).hexdigest())


def qualified_input_hash(manifest_data,page_data,ordinal,tree_data,note_data,accepted_roles):
    manifest=inspect_component_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    ordinal=relation.natural(ordinal,55)
    obj=pending_page(manifest,page_data,ordinal)
    view=encoded(qualified_part(obj,manifest))
    prefix.hashes.inspect_boundaries(view,note_data,accepted_roles)
    if relation.record(view)['role']=='state':tree.inspect_hash_link(tree_data,view,note_data,accepted_roles)
    return view


def qualified_output_hash(manifest_data,page_data,ordinal,output_data,accepted_roles):
    manifest=inspect_component_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    ordinal=relation.natural(ordinal,63)
    if ordinal<55:raise relation.RelationError('T4 output hash ordinal55..62 required')
    obj=pending_page(manifest,page_data,ordinal);view=encoded(qualified_part(obj,manifest))
    output_hash.inspect_boundaries(view,output_data,accepted_roles)
    return view


def qualified_asset_hash(manifest_data,page_data,map_data,accepted_roles):
    manifest=inspect_component_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    obj=pending_page(manifest,page_data,63);view=encoded(qualified_part(obj,manifest))
    map_obj=relation.record(map_data)
    if isinstance(map_obj,dict) and map_obj.get('schema') in ('shieldd-transfer-asset-nonidentity-v1','shieldd-transfer-asset-nonidentity-v2'):
        from . import transfer_asset_generator_nonidentity
        projected=transfer_asset_generator_nonidentity.derived_map_view(map_data,accepted_roles)
        map_data=projected['map_data']
    asset_hash.inspect_boundaries(view,map_data,accepted_roles)
    return view
