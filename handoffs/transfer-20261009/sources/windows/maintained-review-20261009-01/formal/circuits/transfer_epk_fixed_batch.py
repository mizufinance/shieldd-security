"""Single ordered-row replay for the live six-scope EPK48 source capture.

Retained rows stay shared by original index; each page receives only exact
required/materialized rows. This produces construction inputs, not row truth
or legal scalar/point semantics. No canonical scalar rows are assumed here.
"""
from . import transfer_epk_fixed as epk, transfer_epk_fixed_completion as completion
from . import transfer_arithmetic as arithmetic, transfer_relation as relation


def _requirements(checked):
    required={};products=[];squares=[];prefixes=[]
    if len(checked['scopes'])!=6:raise relation.RelationError('EPK batch exact6 scopes')
    for scope_id,scope in enumerate(checked['scopes']):
        lane,slot=('recovery',scope_id) if scope_id<2 else ('encryption',scope_id-2)
        if scope['lane']!=lane or scope['slot']!=slot or len(scope['chunks'])!=8:
            raise relation.RelationError('EPK batch exact scope order/8 pages')
        for local,page in enumerate(scope['chunks']):
            obj=page['metadata'];prefix=f'scope.{scope_id}.page.{local}.'
            if (obj['lane']!=lane or obj['slot']!=slot or obj['window_start']!=16*local or
                obj['window_count']!=min(16,126-16*local) or
                page['qualification_parent_sha256']!=checked['parent_sha256']):
                raise relation.RelationError('EPK batch exact page/parent continuity')
            direct,ps,ss=completion.requirements(page)
            for row,names in direct.items():required.setdefault(row,[]).extend(prefix+name for name in names)
            products.extend((prefix+role,*operands) for role,*operands in ps)
            squares.extend((prefix+role,*operands) for role,*operands in ss)
            prefixes.append(prefix)
    return required,products,squares,prefixes


def _partition(checked,combined,prefixes):
    records=combined.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=32768:
        raise relation.RelationError('EPK batch bounded original32768 rows')
    rows={};previous=-1
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:raise relation.RelationError('EPK batch closed row')
        index=relation.natural(row['row'],200770)
        if index<=previous:raise relation.RelationError('EPK batch original row order/duplicate')
        previous=index;rows[index]=row
        for side in ('a','b'):relation.terms(row[side],262144)
    identity=combined.get('identity',{})
    if (identity.get('relation_digest')!=checked['parent']['relation_digest'] or
        identity.get('domain_size')!=262144 or identity.get('stored_rows')!=200770):
        raise relation.RelationError('EPK batch original replay identity')
    pages=[];covered=set()
    for ordinal,prefix in enumerate(prefixes):
        page=checked['scopes'][ordinal//8]['chunks'][ordinal%8];indices=set()
        for item in combined['templates']:
            if any(name.startswith(prefix) for name in item['roles']):indices.add(item['row'])
        for item in combined['products']:
            if item['role'].startswith(prefix):indices.update(item['rows'])
        if not indices<=set(rows):raise relation.RelationError('EPK batch referenced original row missing')
        extraction=dict(identity=identity,metadata_sha256=page['metadata_sha256'],include_canonical=False,
            selected_rows=[rows[i] for i in sorted(indices)])
        # Recompute actual product/quotient certificates from exact rows. Roles
        # attached to a combined matcher are never accepted as semantic truth.
        completion.selection(page,extraction);covered.update(indices)
        pages.append(dict(ordinal=ordinal,scope_id=ordinal//8,window_start=page['metadata']['window_start'],
            metadata_sha256=page['metadata_sha256'],rows=sorted(indices)))
    if covered!=set(rows):raise relation.RelationError('EPK batch selected original row coverage incomplete')
    return dict(identity=identity,parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        selected_rows=records,pages=pages,ordinary_replays=1,include_canonical=False,
        scope='One independent full ordered-row replay; exact48 bounded EPK row projections; kernel/native/scalar/whole frame OPEN')


def extract_rows(qualified_parent,raw_pages,accepted_capsules,accepted_roles,stream):
    """Root-only: reaccept every typed source page, then consume the relation once."""
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    required,products,squares,prefixes=_requirements(checked);obj=checked['parent']
    combined=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
        required,products,squares,label='epk-all-fixed')
    return _partition(checked,combined,prefixes)


def page_selection(checked,batch,ordinal):
    """Revalidate a persisted shared extraction before existing page construction."""
    relation.natural(ordinal,48)
    if (batch.get('parent_sha256')!=checked['parent_sha256'] or
        batch.get('raw_page_sha256')!=checked['raw_page_sha256'] or batch.get('ordinary_replays')!=1 or
        batch.get('include_canonical') is not False or not isinstance(batch.get('pages'),list) or len(batch['pages'])!=48):
        raise relation.RelationError('EPK batch exact parent/page replay identity')
    descriptor=batch['pages'][ordinal];page=checked['scopes'][ordinal//8]['chunks'][ordinal%8]
    if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','scope_id','window_start','metadata_sha256','rows'} or
        any(type(descriptor[k]) is not int for k in ('ordinal','scope_id','window_start')) or
        descriptor['ordinal']!=ordinal or descriptor['scope_id']!=ordinal//8 or
        descriptor['window_start']!=page['metadata']['window_start'] or descriptor['metadata_sha256']!=page['metadata_sha256']):
        raise relation.RelationError('EPK batch original page descriptor')
    indices=descriptor['rows']
    if not isinstance(indices,list) or not indices or indices!=sorted(set(indices)):
        raise relation.RelationError('EPK batch original row indices')
    records=batch.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=32768:
        raise relation.RelationError('EPK batch retained row bound')
    rows={};previous=-1
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:raise relation.RelationError('EPK batch retained row shape')
        index=relation.natural(row['row'],200770)
        if index<=previous:raise relation.RelationError('EPK batch retained row order')
        previous=index;rows[index]=row
        for side in ('a','b'):relation.terms(row[side],262144)
    if len(rows)!=len(records) or not set(indices)<=set(rows):raise relation.RelationError('EPK batch retained missing/duplicate rows')
    extraction=dict(identity=batch['identity'],metadata_sha256=page['metadata_sha256'],include_canonical=False,
        selected_rows=[rows[i] for i in indices])
    completion.selection(page,extraction)
    return extraction
