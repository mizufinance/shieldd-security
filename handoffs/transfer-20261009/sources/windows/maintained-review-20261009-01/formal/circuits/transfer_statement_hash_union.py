"""Select the thirteen statement-block hash DAGs from one replay of the pinned relation."""
import hashlib
from . import transfer_remaining_pages as pages, transfer_remaining_hash_union as physical
from . import transfer_note_hash as hashes, transfer_arithmetic as arithmetic
from . import transfer_relation as relation

SCHEMA='shieldd-transfer-statement-hash-union-v1'
SCOPE='Thirteen actual statement hash block materializations with pinned parameter/source DAG checks; native/caller/tag/full Transfer joins separate'


def checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
    manifest=pages.inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    if manifest['scope']!='statement' or not isinstance(page_data,(list,tuple)) or len(page_data)!=14:
        raise relation.RelationError('exact fourteen-page statement hash scope')
    role=pages.inspect_page(manifest_data,page_data[0],0,accepted_roles)
    shared=dict(role['observed'])
    for ordinal in range(1,14):
        checked=pages.inspect_page(manifest_data,page_data[ordinal],ordinal,accepted_roles,parameter_root)
        if (checked['records']!=role['records'] or checked['metadata']['calls']!=role['metadata']['calls']
                or any(checked['metadata'][key]!=role['metadata'][key] for key in pages.IDENTITY)
                or checked['graph']['width']!=6):
            raise relation.RelationError('same routing role/source/identity and actual hash width')
        for handle,lc in checked['observed'].items():
            if handle in shared and shared[handle]!=lc:
                raise relation.RelationError('statement hash cross-page LC changed')
            shared[handle]=lc
        yield ordinal,checked


def extract(manifest_data,page_data,stream,accepted_roles,parameter_root):
    required={};products=[];identities={};obj=None
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        obj=checked['metadata'];identities[str(ordinal)]=checked['metadata_sha256']
        direct,nonlinear=physical._requirements(checked);prefix=str(ordinal)+'.'
        for row,names in direct.items():required.setdefault(row,[]).extend(prefix+name for name in names)
        products.extend((prefix+name,minus,plus,output) for name,minus,plus,output in nonlinear)
    combined=physical._retain(stream,obj,required,products)
    rows={row['row']:row for row in combined['selected_rows']};parts={}
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        prefix=str(ordinal)+'.';templates=[];nonlinear=[];used=set()
        for item in combined['templates']:
            names=[name.removeprefix(prefix) for name in item['roles'] if name.startswith(prefix)]
            if names:templates.append(dict(roles=names,row=item['row']));used.add(item['row'])
        for item in combined['products']:
            if item['role'].startswith(prefix):
                nonlinear.append(dict(role=item['role'].removeprefix(prefix),rows=item['rows']));used.update(item['rows'])
        meta=checked['metadata']
        parts[str(ordinal)]=dict(identity=combined['identity'],templates=templates,products=nonlinear,
            selected_rows=[rows[index] for index in sorted(used)],metadata_sha256=identities[str(ordinal)],
            slot=meta['slot'],role=meta['role'],level=meta['level'],block=meta['block'],scope=SCOPE)
    result=dict(schema=SCHEMA,scope='statement',identity=combined['identity'],parts=parts,
        selected_rows=combined['selected_rows'],manifest_sha256=hashlib.sha256(manifest_data).hexdigest(),
        page_sha256=[hashlib.sha256(data).hexdigest() for data in page_data],ordinary_replays=1,semantic_scope=SCOPE)
    validate(manifest_data,page_data,result,accepted_roles,parameter_root)
    return result


def validate(manifest_data,page_data,extracted,accepted_roles,parameter_root):
    if (not isinstance(extracted,dict) or set(extracted)!={'schema','scope','identity','parts','selected_rows',
            'manifest_sha256','page_sha256','ordinary_replays','semantic_scope'}
            or extracted['schema']!=SCHEMA or extracted['scope']!='statement' or extracted['semantic_scope']!=SCOPE
            or type(extracted['ordinary_replays']) is not int or extracted['ordinary_replays']!=1
            or extracted['manifest_sha256']!=hashlib.sha256(manifest_data).hexdigest()
            or extracted['page_sha256']!=[hashlib.sha256(data).hexdigest() for data in page_data]
            or not isinstance(extracted['parts'],dict) or set(extracted['parts'])!={str(i) for i in range(1,14)}):
        raise relation.RelationError('closed exact statement hash derivative')
    role=pages.inspect_page(manifest_data,page_data[0],0,accepted_roles)
    arithmetic.normalize_selection({**extracted,'metadata_sha256':role['metadata_sha256']},role['metadata'],role['metadata_sha256'])
    used=set();raw={row['row']:row for row in extracted['selected_rows']}
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        part=extracted['parts'][str(ordinal)]
        if (not isinstance(part,dict) or set(part)!={'identity','templates','products','selected_rows',
                'metadata_sha256','slot','role','level','block','scope'}
                or part['identity']!=extracted['identity'] or part['scope']!=SCOPE):
            raise relation.RelationError('statement hash exact part shape/identity')
        arithmetic.normalize_selection(part,checked['metadata'],checked['metadata_sha256'])
        direct,products=physical._requirements(checked)
        expected=physical._match_part(part['selected_rows'],direct,products)
        inventory=lambda value: sorted((item['row'],tuple(sorted(item['roles']))) for item in value)
        products_inventory=lambda value: sorted((item['role'],tuple(item['rows'])) for item in value)
        if (inventory(part['templates'])!=inventory(expected['templates'])
                or products_inventory(part['products'])!=products_inventory(expected['products'])
                or part['selected_rows']!=expected['selected_rows']):
            raise relation.RelationError('statement hash exact physical source templates changed')
        hashes._select_permutation(checked,part,parameter_root,role_prefix='remaining')
        for row in part['selected_rows']:
            if raw.get(row['row'])!=row:raise relation.RelationError('statement hash union physical row changed')
            used.add(row['row'])
    if not 1<=len(raw)<=physical.MAX_ROWS or len(raw)!=len(extracted['selected_rows']) or used!=set(raw):
        raise relation.RelationError('statement hash exact full physical coverage')
    return extracted
