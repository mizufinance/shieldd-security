"""Bounded qualified page ingress; every page still needs source and actual rows.

Manifest qualification comes from full ordered ordinary2+repeat comparison.
Page digests bind pending bytes, never replace the independent native/DAG/row
checks in transfer_note_hash. This adapter produces no qualification itself.
"""
import json
from blake3 import blake3
from . import transfer_relation as relation,transfer_note_hash as hashes

SCOPE='55 bounded input-note permutation pages from one lowering; tree wiring/native joins open'


def inventory():
    result=[]
    for slot in range(2):
        result.extend((slot,'commitment',0,block) for block in range(2))
        result.append((slot,'nullifier',0,0))
        result.extend((slot,'state',level,0) for level in range(24))
        if slot:result.append((slot,'dummy',0,0))
    return result


def inspect_manifest(data,expected_relation):
    if not isinstance(data,bytes) or len(data)>128*1024:raise relation.RelationError('note hash manifest byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
          'ordinary_full_ordered_rows_equal','repeated_observations_equal','pages'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=('shieldd-transfer-note-hash-pages-v1','transfer',SCOPE):
        raise relation.RelationError('note hash pages closed schema/scope')
    if obj['relation_digest']!=expected_relation or obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True:
        raise relation.RelationError('note hash pages identity/pending qualification')
    size=relation.natural(obj['domain_size']);count=relation.natural(obj['full_rows']);copy=relation.natural(obj['constant_copy'],size)
    if size<4 or size&(size-1) or not 0<count<=size or copy<3:raise relation.RelationError('note hash pages shape')
    if not isinstance(obj['pages'],list) or len(obj['pages'])!=55:raise relation.RelationError('note hash pages truncated/overflow inventory')
    for ordinal,(descriptor,wanted) in enumerate(zip(obj['pages'],inventory())):
        if not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','slot','role','level','block','blake3'}:
            raise relation.RelationError('note hash page descriptor shape')
        if (relation.natural(descriptor['ordinal'])!=ordinal or
            (relation.natural(descriptor['slot'],2),descriptor['role'],relation.natural(descriptor['level'],24),relation.natural(descriptor['block'],2))!=wanted):
            raise relation.RelationError('note hash pages native role order/duplicate')
        digest=descriptor['blake3']
        if not isinstance(digest,str) or len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):
            raise relation.RelationError('note hash page digest encoding')
    return obj


def qualified_page(manifest_data,page_data,ordinal,note_data,accepted_roles):
    """Verified view under an ALREADY qualified manifest; does not write evidence."""
    accepted=hashes.notes.inspect_metadata(note_data,accepted_roles)
    manifest=inspect_manifest(manifest_data,accepted['metadata']['relation_digest'])
    ordinal=relation.natural(ordinal,55)
    if not isinstance(page_data,bytes) or len(page_data)>4*1024*1024:raise relation.RelationError('note hash page byte bound')
    descriptor=manifest['pages'][ordinal]
    if blake3(page_data).hexdigest()!=descriptor['blake3']:raise relation.RelationError('note hash page bytes/digest mismatch')
    obj=relation.record(page_data)
    if obj.get('ordinary_full_ordered_rows_equal') is not False or obj.get('repeated_observations_equal') is not False:
        raise relation.RelationError('note hash page must retain pending flags')
    if any(obj.get(key)!=manifest[key] for key in ('relation_digest','domain_size','full_rows','constant_copy')) or any(obj.get(key)!=descriptor[key] for key in ('slot','role','level','block')):
        raise relation.RelationError('note hash page/manifest role or identity mismatch')
    # Only this in-memory view inherits the proven full-row/repeat qualification.
    view=dict(obj,ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
    data=(json.dumps(view,separators=(',',':'))+'\n').encode()
    hashes.inspect_boundaries(data,note_data,accepted_roles)
    return data
