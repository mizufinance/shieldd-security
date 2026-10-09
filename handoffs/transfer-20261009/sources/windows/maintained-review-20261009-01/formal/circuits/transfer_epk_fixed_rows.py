"""One original replay for fixed48, six canonical chains and EPK boundaries.

Published/computed bindings and inverse products are selected from real rows.
The native SDK seed, fixed endpoint proof and outside-row frame remain separate
constructive prerequisites. This module never accepts their desired equations.
"""
from . import transfer_epk_fixed as epk, transfer_epk_fixed_batch as batch
from . import transfer_epk_fixed_canonical as scalar, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index

SCHEMA='shieldd-transfer-epk-boundary-row-derivative-v1'


def _roles(checked):
    scopes=[]
    for scope_id,scope in enumerate(checked['scopes']):
        page=scope['chunks'][0];metadata=page['metadata']
        def value(ref):
            if 'source' in ref:return page['expressions'][source_index(ref['source'])]
            return canonical([(0,epk.fixed._native(ref))])
        published=tuple(value(ref) for ref in metadata['published'])
        computed=tuple(value(ref) for ref in metadata['output'])
        inverse=value(metadata['inverse'])
        if (len(inverse)!=1 or inverse[0][1]!=1 or inverse[0][0]==0
                or len(published[0])!=1 or published[0][0][1]!=1
                or inverse[0][0]==published[0][0][0]):
            raise relation.RelationError('EPK boundary exact distinct inverse/published-x witnesses')
        scopes.append(dict(scope_id=scope_id,published=published,computed=computed,inverse=inverse))
    return scopes


def _requirements(checked):
    copy=checked['parent']['constant_copy'];outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['boundary.constant-copy']};products=[]
    for scope in _roles(checked):
        prefix=f"boundary.scope.{scope['scope_id']}."
        for axis,(published,computed) in enumerate(zip(scope['published'],scope['computed'])):
            equation=outline(combine(published,computed,-1))
            if equation:required.setdefault((equation,()),[]).append(prefix+f'bind.{axis}')
        q=scope['inverse'];x=scope['published'][0]
        products.append((prefix+'inverse',outline(combine(q,x,-1)),outline(combine(q,x)),None,((copy,1),)))
    return required,products,[]


def _subset(combined,predicate):
    templates=[dict(item,roles=[role for role in item['roles'] if predicate(role)])
        for item in combined['templates'] if any(predicate(role) for role in item['roles'])]
    products=[item for item in combined['products'] if predicate(item['role'])]
    indices={item['row'] for item in templates}|{index for item in products for index in item['rows']}
    return dict(identity=combined['identity'],templates=templates,products=products,
        selected_rows=[row for row in combined['selected_rows'] if row['row'] in indices])


def _certificates(checked,extracted):
    if (not isinstance(extracted,dict) or extracted.get('schema')!=SCHEMA
            or extracted.get('parent_sha256')!=checked['parent_sha256']
            or extracted.get('raw_page_sha256')!=checked['raw_page_sha256']):
        raise relation.RelationError('EPK boundary exact parent/page identity')
    raw,normalized=arithmetic.normalize_selection(extracted,checked['parent'],checked['parent_sha256'])
    if len(raw)>64:raise relation.RelationError('EPK boundary bounded64 original rows')
    copy=checked['parent']['constant_copy']
    copies=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(copies)!=1:raise relation.RelationError('EPK boundary exact original constant link')
    covered=set(copies);scopes=[]
    for scope in _roles(checked):
        bindings=[]
        for axis,(published,computed) in enumerate(zip(scope['published'],scope['computed'])):
            equation=combine(published,computed,-1)
            if not equation:bindings.append(dict(axis=axis,kind='same-lc',rows=[]));continue
            matching=[(i,row[0]!=equation) for i,row in normalized.items()
                if not row[1] and row[0] in (equation,canonical((c,-v) for c,v in equation))]
            if len(matching)!=1:raise relation.RelationError('EPK boundary unique selected coordinate assertion')
            row,negative=matching[0];covered.add(row)
            bindings.append(dict(axis=axis,kind='assertion',rows=[row],negative=negative,equation=equation))
        inverse=arithmetic.quotient_certificate(((0,1),),scope['published'][0],scope['inverse'],normalized)
        if inverse['kind']!='product' or len(inverse['rows'])!=3:
            raise relation.RelationError('EPK boundary exact actual inverse triple')
        covered.update(inverse['rows'])
        expected=(combine(inverse['output'],((0,1),),-1),())
        assertion=inverse['rows'][-1];negative=normalized[assertion]!=expected
        constructor_rows=dict(normalized)
        if negative:
            if normalized[assertion]!=(canonical((c,-v) for c,v in expected[0]),()):
                raise relation.RelationError('EPK boundary original inverse assertion sign')
            constructor_rows[assertion]=expected
        constructor=arithmetic.completion_certificate(inverse,constructor_rows)
        if constructor is None:raise relation.RelationError('EPK boundary supported three-write inverse constructor')
        scopes.append(dict(scope,bindings=bindings,inverse_certificate=inverse,
            inverse_assertion_negative=negative,inverse_constructor=constructor))
    if set(raw)!=covered:raise relation.RelationError('EPK boundary exact original coverage')
    return raw,scopes


def boundary_selection(checked,combined):
    selected=_subset(combined,lambda name:name.startswith('boundary.'))
    result=dict(schema=SCHEMA,parent_sha256=checked['parent_sha256'],
        raw_page_sha256=checked['raw_page_sha256'],identity=selected['identity'],
        metadata_sha256=checked['parent_sha256'],selected_rows=selected['selected_rows'])
    _certificates(checked,result)
    return result


def extract_rows(qualified_parent,raw_pages,accepted_capsules,accepted_roles,stream):
    """Root-only, all three actual row projections from one full replay."""
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    boundaries=scalar._boundaries(checked)
    tap=scalar._CandidateStream(stream,boundaries,checked['parent']['constant_copy'])
    required,products,squares,prefixes=batch._requirements(checked)
    direct,more_products,more_squares=_requirements(checked)
    for row,names in direct.items():required.setdefault(row,[]).extend(names)
    products.extend(more_products);squares.extend(more_squares);metadata=checked['parent']
    combined=arithmetic.extract_templates(tap,metadata['relation_digest'],metadata['domain_size'],metadata['full_rows'],
        required,products,squares,label='epk-all-fixed-canonical-boundaries')
    if not tap.eof or not tap.tail_checked:raise relation.RelationError('EPK row join incomplete ordinary lifecycle')
    fixed=batch._partition(checked,_subset(combined,lambda name:name.startswith('scope.')),prefixes)
    canonical_rows=scalar._derive(checked,boundaries,combined['identity'],tap.raw,tap.normalized,tap.records)
    result=dict(fixed=fixed,canonical=canonical_rows,boundaries=boundary_selection(checked,combined),
        parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],ordinary_replays=1,
        scope='Actual row projections only; canonical/local/native endpoint/inverse proofs and original outside frame OPEN')
    return result


def boundary_plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted):
    """Finite inverse writes and signed coordinate bindings; no row truth premise."""
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    raw,scopes=_certificates(checked,extracted);owned=set();protected={0,1,2,checked['parent']['constant_copy']}
    for scope in checked['scopes']:
        page=scope['chunks'][0];metadata=page['metadata']
        for ref in [metadata['randomizer'],*metadata['published'],*metadata['output']]:
            if 'source' in ref:protected.update(c for c,_ in page['expressions'][source_index(ref['source'])])
        protected.update(c for bit in metadata['bits'] for c,_ in page['expressions'][source_index(bit)])
    for scope in scopes:
        stage=scope['inverse_constructor'];writes={stage[k] for k in ('quotient','product','auxiliary')}
        if writes&(owned|protected):raise relation.RelationError('EPK boundary inverse writes alias shared inputs/points')
        # Independent scopes must not destroy a prior inverse materialization.
        previous_support={c for previous in scopes[:scope['scope_id']]
            for index in previous['inverse_certificate']['rows'] for lc in raw[index] for c,_ in lc}
        if writes&previous_support:raise relation.RelationError('EPK boundary inverse writes alias prior scope row support')
        owned.update(writes)
    return dict(parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        identity=extracted['identity'],scopes=scopes,writes=sorted(owned),protected=sorted(protected),
        prerequisite='Seed published coordinates from same SDK generator/scalar; derive x reciprocal legality from canonical0<n<ORDER and global exact generator order. Fixed native recurrence derives coordinate bindings.',
        universal_frame='Three-write constructors preserve every outside column; exact signed assertion/row transport follows finite certificates.',
        scope='Original inverse/binding construction inputs only; SDK/native/fixed endpoint and whole frame proofs OPEN')
