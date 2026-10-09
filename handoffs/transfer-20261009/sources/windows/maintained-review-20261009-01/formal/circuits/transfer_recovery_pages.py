"""Strict74 views over exact retained65 prefix,8 hashes and capsule roles.

No runtime qualification is created here. The caller supplies the qualified
four-spool manifest, and every page retains its original pending byte identity.
"""
import hashlib
from . import transfer_t4_pages as retained,transfer_relation as relation
from . import transfer_recovery_capsule as capsules,transfer_recovery_hash as hashes
from .transfer_note_t4_pages import encoded

SCOPE='retained65 pages plus8 recovery hashes and1 recovery roles page from one lowering; native/kernel joins open'


def inventory():
    return retained.inventory()+[(slot,role,0,0) for slot in range(2) for role in hashes.ROLES]+[(0,'recovery-roles',0,0)]


def retained_manifest(obj):
    return dict(obj,schema='shieldd-transfer-t4-pages-v1',scope=retained.SCOPE,pages=obj['pages'][:65])


def inspect_manifest(data,expected_relation):
    if not isinstance(data,bytes) or len(data)>128*1024:raise relation.RelationError('recovery74 manifest byte bound')
    obj=relation.record(data)
    if not isinstance(obj,dict) or (obj.get('schema'),obj.get('scope'))!=('shieldd-transfer-t4-recovery-pages-v1',SCOPE):
        raise relation.RelationError('recovery74 schema/scope')
    pages=obj.get('pages')
    if not isinstance(pages,list) or len(pages)!=74:raise relation.RelationError('recovery74 exact inventory')
    retained.inspect_manifest(encoded(retained_manifest(obj)),expected_relation)
    for ordinal,(descriptor,wanted) in enumerate(zip(pages,inventory())):
        if not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','slot','role','level','block','blake3'} or any(type(descriptor[k]) is not int for k in ('ordinal','slot','level','block')):
            raise relation.RelationError('recovery74 closed descriptor')
        if (descriptor['ordinal'],descriptor['slot'],descriptor['role'],descriptor['level'],descriptor['block'])!=(ordinal,*wanted):
            raise relation.RelationError('recovery74 exact native descriptor order')
        digest=descriptor['blake3']
        if not isinstance(digest,str) or len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):
            raise relation.RelationError('recovery74 digest encoding')
    return obj


def qualified_prefix65_view(manifest_data,expected_relation):
    """Derivative receipt over an actual74 parent, never an actual65 capture.

Keep the parent schema, bytes, qualification flags and all74 descriptors. The
consumer routes ordinal0..64 using transfer_t4_pages directly on parent_data.
No file or new qualification flag is created by this function.
"""
    parent=inspect_manifest(manifest_data,expected_relation)
    return dict(kind='derived65-prefix-of-qualified74',parent_data=manifest_data,
        parent_metadata_sha256=hashlib.sha256(manifest_data).hexdigest(),parent_manifest=parent,
        prefix_descriptors=tuple(dict(d) for d in parent['pages'][:65]),
        ordinary_full_ordered_rows_equal=parent['ordinary_full_ordered_rows_equal'],
        repeated_observations_equal=parent['repeated_observations_equal'])


def qualified_roles(manifest_data,page_data,output_data,accepted_roles):
    manifest=inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    obj=retained.pending_page(manifest,page_data,73,role_fields=False)
    view=encoded(retained.qualified_part(obj,manifest))
    capsules.inspect_metadata(view,output_data,accepted_roles)
    return view,hashlib.sha256(page_data).hexdigest()


def qualified_hash(manifest_data,page_data,ordinal,recovery_data,output_data,accepted_roles,parameter_root):
    manifest=inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    ordinal=relation.natural(ordinal,73)
    if ordinal<65:raise relation.RelationError('recovery74 hash ordinal65..72 required')
    obj=retained.pending_page(manifest,page_data,ordinal)
    view=encoded(retained.qualified_part(obj,manifest))
    hashes.inspect_metadata(view,recovery_data,output_data,accepted_roles,parameter_root)
    return view
