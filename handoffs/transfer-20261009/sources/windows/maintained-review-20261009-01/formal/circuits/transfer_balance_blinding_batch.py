"""One full ordinary replay for the distinct eight-page blinding capture.

Original rows are shared by physical index. Product/quotient correspondence is
recomputed from the retained exact rows for every page, never from role labels.
"""
from . import transfer_balance_blinding_fixed as ingress,transfer_balance_blinding_completion as completion
from . import transfer_relation as relation,transfer_arithmetic as arithmetic


def requirements(checked):
    if len(checked.get('chunks',[]))!=8:raise relation.RelationError('balance blinding exact8 pages required')
    required={};products=[];squares=[]
    for ordinal,page in enumerate(checked['chunks']):
        obj=page['metadata'];prefix=f'page.{ordinal}.'
        if (obj['window_start'],obj['window_count'],page['qualification_parent_sha256'])!=(16*ordinal,min(16,126-16*ordinal),checked['parent_sha256']):
            raise relation.RelationError('balance blinding page/parent continuity')
        direct,ps,ss=completion.requirements(page)
        for row,names in direct.items():required.setdefault(row,[]).extend(prefix+name for name in names)
        products.extend((prefix+role,*operands) for role,*operands in ps)
        squares.extend((prefix+role,*operands) for role,*operands in ss)
    return required,products,squares


def _records(extracted):
    records=extracted.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=16384:raise relation.RelationError('balance blinding original16384 row bound')
    rows={};previous=-1
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:raise relation.RelationError('balance blinding original closed row')
        index=relation.natural(row['row'],200770)
        if index<=previous:raise relation.RelationError('balance blinding original row order')
        previous=index;rows[index]=row
        for side in ('a','b'):relation.terms(row[side],262144)
    return rows


def extract_rows(qualified_parent,raw_pages,expected_base,expected_blinding,stream):
    """Root-only one ordered production relation stream, after actual qualification."""
    checked=ingress.inspect_pages(qualified_parent,raw_pages,expected_base,expected_blinding)
    required,products,squares=requirements(checked)
    combined=arithmetic.extract_templates(stream,ingress.DIGEST,262144,200770,required,products,squares,label='balance-blinding-fixed')
    rows=_records(combined);descriptors=[];covered=set()
    for ordinal,page in enumerate(checked['chunks']):
        prefix=f'page.{ordinal}.';indices=set()
        for item in combined['templates']:
            if any(role.startswith(prefix) for role in item['roles']):indices.add(item['row'])
        for item in combined['products']:
            if item['role'].startswith(prefix):indices.update(item['rows'])
        if not indices<=rows.keys():raise relation.RelationError('balance blinding selected original row missing')
        selection=dict(identity=combined['identity'],metadata_sha256=page['metadata_sha256'],include_canonical=False,
            selected_rows=[rows[i] for i in sorted(indices)])
        completion.selection(page,selection);covered.update(indices)
        descriptors.append(dict(ordinal=ordinal,window_start=16*ordinal,metadata_sha256=page['metadata_sha256'],rows=sorted(indices)))
    if covered!=rows.keys():raise relation.RelationError('balance blinding original coverage incomplete')
    return dict(identity=combined['identity'],parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        ordinary_replays=1,include_canonical=False,selected_rows=combined['selected_rows'],pages=descriptors,
        scope='One genuine full ordered relation replay;8 blinding row projections; canonical/native126/full balance OPEN')


def page_selection(checked,extracted,ordinal):
    relation.natural(ordinal,8);rows=_records(extracted)
    if (extracted.get('parent_sha256')!=checked['parent_sha256'] or extracted.get('raw_page_sha256')!=checked['raw_page_sha256'] or
        type(extracted.get('ordinary_replays'))is not int or extracted['ordinary_replays']!=1 or extracted.get('include_canonical')is not False or
        not isinstance(extracted.get('pages'),list) or len(extracted['pages'])!=8):
        raise relation.RelationError('balance blinding retained actual replay/parent identity')
    descriptor=extracted['pages'][ordinal];page=checked['chunks'][ordinal]
    if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','window_start','metadata_sha256','rows'} or
        type(descriptor['ordinal'])is not int or descriptor['ordinal']!=ordinal or type(descriptor['window_start'])is not int or
        descriptor['window_start']!=16*ordinal or descriptor['metadata_sha256']!=page['metadata_sha256']):
        raise relation.RelationError('balance blinding original page descriptor')
    indices=descriptor['rows']
    if (not isinstance(indices,list) or not indices or any(type(i)is not int for i in indices) or
        indices!=sorted(set(indices)) or not set(indices)<=rows.keys()):
        raise relation.RelationError('balance blinding actual selected indices')
    selection=dict(identity=extracted['identity'],metadata_sha256=page['metadata_sha256'],include_canonical=False,
        selected_rows=[rows[i] for i in indices]);completion.selection(page,selection);return selection
