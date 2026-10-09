"""Typed all-five balance129 projections from one complete original replay.

Shared original rows retain indices and raw terms. Actual product/auxiliary,
square and quotient assertions are rechecked for each local formula. This is
neither a native point truth premise nor a full original-frame certificate.
"""
from . import transfer_balance_variable as variable, transfer_balance_variable_completion as completion
from . import transfer_arithmetic as arithmetic, transfer_relation as relation
from .transfer_balance_rows import canonical

SCHEMA='shieldd-transfer-balance-variable-row-batch-v1'


def _requirements(checked,include_bits):
    required={};products=[];squares=[]
    for ordinal,chunk in enumerate(checked['chunks']):
        prefix=f'page.{ordinal}.'
        direct,ps,ss=variable.row_requirements(chunk,checked['parent']['relation_digest'],include_bits=include_bits)
        for row,names in direct.items():required.setdefault(row,[]).extend(prefix+name for name in names)
        products.extend((prefix+role,*operands) for role,*operands in ps)
        squares.extend((prefix+role,*operands) for role,*operands in ss)
    return required,products,squares


def _selection(chunk,extracted,include_bits):
    raw,normalized=arithmetic.normalize_selection(extracted,chunk['metadata'],chunk['metadata_sha256'])
    required,products,squares=variable.row_requirements(chunk,chunk['metadata']['relation_digest'],include_bits=include_bits)
    expected_roles={role:target for target,names in required.items() for role in names}
    seen=set()
    for item in extracted.get('templates',[]):
        if not isinstance(item,dict) or set(item)!={'roles','row'} or not isinstance(item['roles'],list) or not item['roles']:
            raise relation.RelationError('balance batch closed local template certificate')
        index=relation.natural(item['row'],chunk['metadata']['full_rows'])
        if index not in raw:raise relation.RelationError('balance batch local template row absent')
        for role in item['roles']:
            if not isinstance(role,str) or role in seen or role not in expected_roles:
                raise relation.RelationError('balance batch exact local template roles')
            seen.add(role);target=expected_roles[role]
            if raw[index] not in (target,(canonical((c,-v) for c,v in target[0]),target[1])):
                raise relation.RelationError('balance batch local template original equation')
    if seen!=set(expected_roles):raise relation.RelationError('balance batch complete local template roles')
    expected_products={item[0] for item in products+squares};seen=set()
    for item in extracted.get('products',[]):
        if (not isinstance(item,dict) or set(item)!={'role','rows'} or not isinstance(item['role'],str)
                or item['role'] in seen or item['role'] not in expected_products or not isinstance(item['rows'],list)
                or not 1<=len(item['rows'])<=3):
            raise relation.RelationError('balance batch closed exact product roles')
        seen.add(item['role'])
        for index in item['rows']:
            relation.natural(index,chunk['metadata']['full_rows'])
            if index not in raw:raise relation.RelationError('balance batch local product row absent')
    if seen!=expected_products:raise relation.RelationError('balance batch complete local product roles')
    covered=set()
    for target,names in required.items():
        matches=[index for index,row in raw.items() if row==target or
            not target[1] and row==(canonical((c,-v) for c,v in target[0]),())]
        if not matches:raise relation.RelationError('balance batch actual direct row missing: '+names[0])
        covered.update(matches)
    for offset in range(chunk['metadata']['window_count']):
        certificate=completion.cone_certificates(chunk,extracted,offset,include_precompute=True)
        covered.update(certificate['rows'])
        covered.update(index for item in certificate['quotients']['certificates'] for index in item['rows'])
    if set(raw)!=covered:raise relation.RelationError('balance batch local original row coverage')
    return extracted


def _partition(checked,combined,include_bits):
    if type(include_bits)is not bool:raise relation.RelationError('balance batch Boolean bit extraction flag')
    identity=combined.get('identity',{});parent=checked['parent']
    if (identity.get('relation_digest')!=parent['relation_digest'] or identity.get('domain_size')!=parent['domain_size']
            or identity.get('stored_rows')!=parent['full_rows']):
        raise relation.RelationError('balance batch complete ordinary relation identity')
    records=combined.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=32768:
        raise relation.RelationError('balance batch shared original32768 row bound')
    rows={};previous=-1
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:raise relation.RelationError('balance batch closed original row')
        index=relation.natural(row['row'],parent['full_rows'])
        if index<=previous:raise relation.RelationError('balance batch ordered unique original rows')
        previous=index;rows[index]=row
        for side in ('a','b'):relation.terms(row[side],parent['domain_size'])
    pages=[];covered=set()
    for ordinal,chunk in enumerate(checked['chunks']):
        prefix=f'page.{ordinal}.';indices={item['row'] for item in combined['templates']
            if any(role.startswith(prefix) for role in item['roles'])}
        indices.update(index for item in combined['products'] if item['role'].startswith(prefix) for index in item['rows'])
        if not indices<=set(rows):raise relation.RelationError('balance batch referenced original row absent')
        templates=[dict(row=item['row'],roles=[name[len(prefix):] for name in item['roles'] if name.startswith(prefix)])
            for item in combined['templates'] if any(name.startswith(prefix) for name in item['roles'])]
        products=[dict(role=item['role'][len(prefix):],rows=item['rows']) for item in combined['products'] if item['role'].startswith(prefix)]
        selected=dict(identity=identity,metadata_sha256=chunk['metadata_sha256'],templates=templates,products=products,
            signed_parent_metadata_sha256=chunk['signed_parent_metadata_sha256'],selected_rows=[rows[i] for i in sorted(indices)])
        _selection(chunk,selected,include_bits);covered.update(indices)
        pages.append(dict(ordinal=ordinal,window_start=chunk['metadata']['window_start'],
            window_count=chunk['metadata']['window_count'],metadata_sha256=chunk['metadata_sha256'],rows=sorted(indices),
            templates=templates,products=products))
    if len(pages)!=5 or covered!=set(rows):raise relation.RelationError('balance batch exact five original projections/coverage')
    return dict(schema=SCHEMA,parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        identity=identity,include_bits=include_bits,selected_rows=records,pages=pages,ordinary_replays=1,
        scope='Five typed65-window/129-bit source and exact original row projections; native/constructive/full frame OPEN')


def extract_rows(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base,stream,*,include_bits=False):
    """Root-only full ordinary replay once for all five typed raw pages."""
    checked=variable.inspect_pages(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base)
    required,products,squares=_requirements(checked,include_bits)
    parent=checked['parent']
    combined=arithmetic.extract_templates(stream,expected_relation,parent['domain_size'],parent['full_rows'],
        required,products,squares,label='balance-all-five')
    return _partition(checked,combined,include_bits)


def page_selection(checked,extracted,ordinal):
    """Recheck persisted parent, original row order and local source semantics."""
    ordinal=relation.natural(ordinal,5)
    if (not isinstance(extracted,dict) or extracted.get('schema')!=SCHEMA or
            extracted.get('parent_sha256')!=checked['parent_sha256'] or
            extracted.get('raw_page_sha256')!=checked['raw_page_sha256'] or
            type(extracted.get('ordinary_replays'))is not int or extracted['ordinary_replays']!=1 or
            type(extracted.get('include_bits'))is not bool or not isinstance(extracted.get('pages'),list) or len(extracted['pages'])!=5):
        raise relation.RelationError('balance batch persisted parent/page/replay identity')
    page=extracted['pages'][ordinal];chunk=checked['chunks'][ordinal]
    if (not isinstance(page,dict) or set(page)!={'ordinal','window_start','window_count','metadata_sha256','rows','templates','products'} or
            any(type(page[key])is not int or page[key]!=value for key,value in
                [('ordinal',ordinal),('window_start',chunk['metadata']['window_start']),('window_count',chunk['metadata']['window_count'])]) or
            page['metadata_sha256']!=chunk['metadata_sha256'] or not isinstance(page['rows'],list) or
            not page['rows'] or page['rows']!=sorted(set(page['rows']))):
        raise relation.RelationError('balance batch exact persisted page descriptor')
    parent=checked['parent'];identity=extracted.get('identity',{})
    if any(identity.get(key)!=parent[parent_key] for key,parent_key in
        [('relation_digest','relation_digest'),('domain_size','domain_size'),('stored_rows','full_rows')]):
        raise relation.RelationError('balance batch persisted full ordinary identity')
    records=extracted.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=32768:raise relation.RelationError('balance batch persisted row bound')
    rows={};previous=-1
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:raise relation.RelationError('balance batch persisted row shape')
        index=relation.natural(row['row'],parent['full_rows'])
        if index<=previous:raise relation.RelationError('balance batch persisted row order')
        previous=index;rows[index]=row
        for side in ('a','b'):relation.terms(row[side],parent['domain_size'])
    if not set(page['rows'])<=set(rows):raise relation.RelationError('balance batch persisted row missing')
    selected=dict(identity=identity,metadata_sha256=chunk['metadata_sha256'],templates=page['templates'],products=page['products'],
        signed_parent_metadata_sha256=chunk['signed_parent_metadata_sha256'],selected_rows=[rows[i] for i in page['rows']])
    return _selection(chunk,selected,extracted['include_bits'])
