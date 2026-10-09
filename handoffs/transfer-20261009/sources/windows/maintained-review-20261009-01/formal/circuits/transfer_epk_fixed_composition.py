"""Exact six-loop construction ownership plan from qualified EPK48 + actual rows.

The local row constructors and native scalar/point seed proofs are separate
kernel obligations. This plan supplies their actual footprints/adjacency and
universal outside-preservation data; it never assumes final row/output truth.
"""
from . import transfer_epk_fixed as epk,transfer_epk_fixed_batch as batch
from . import transfer_epk_fixed_completion as completion,transfer_relation as relation
from .transfer_balance_rows import source_index


def _loop_kept(page_kept,writes,protected):
    """Page inputs include private earlier accumulators; caller roles do not.

    Exact prior rows still enter the write freshness check above. Removing a
    private written column from global kept never removes its earlier rows.
    """
    if writes&protected:raise relation.RelationError('EPK sequence writes alias actual caller/shared roles')
    return sorted(page_kept-writes)


def plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted):
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    scope_lcs=[]
    for scope in checked['scopes']:
        first=scope['chunks'][0];obj=first['metadata'];lcs=[]
        for ref in [obj['randomizer'],obj['inverse'],*obj['published'],*obj['output']]:
            if 'source' in ref:lcs.append(first['expressions'][source_index(ref['source'])])
        lcs.extend(first['expressions'][source_index(bit)] for bit in obj['bits']);scope_lcs.append(lcs)
    loops=[];owned=set();prior_rows=set();prior_support=set();all_rows=set()
    for scope_id,scope in enumerate(checked['scopes']):
        programs=[];initial_rows=set();kept=set();loop_writes=set();local_rows=set()
        readonly=tuple(lc for other,lcs in enumerate(scope_lcs) if other!=scope_id for lc in lcs)
        first_page=scope['chunks'][0];metadata=first_page['metadata']
        current_output={source_index(ref['source']) for ref in metadata['output'] if 'source' in ref}
        protected={0,1,2,metadata['constant_copy']}
        for owner in (accepted_capsules,accepted_roles):
            protected.update(c for handle,terms in owner['observed'].items() if handle not in current_output for c,_ in terms)
        for ref in [metadata['randomizer'],metadata['inverse'],*metadata['published']]:
            if 'source' in ref:protected.update(c for c,_ in first_page['expressions'][source_index(ref['source'])])
        protected.update(c for bit in metadata['bits'] for c,_ in first_page['expressions'][source_index(bit)])
        protected.update(c for terms in list(readonly)+list(first_page['points'][0][0]) for c,_ in terms)
        for local,chunk in enumerate(scope['chunks']):
            ordinal=8*scope_id+local;selection=batch.page_selection(checked,extracted,ordinal)
            construction=completion.completion_plan(chunk,selection,accepted_capsules,accepted_roles,readonly_lcs=readonly)
            raw={row['row']:row for row in selection['selected_rows']};initial_rows.update(construction['initial_rows'])
            kept.update(construction['kept']);local_rows.update(raw);all_rows.update(raw)
            for window in construction['windows']:
                stages=window['stages'];writes=set();rows=set()
                for stage in stages:
                    current=({stage['output']} if stage['kind']=='linear' else
                        {stage['output'],stage['auxiliary']} if stage['kind']=='product' else
                        {stage['quotient'],stage['product'],stage['auxiliary']})
                    if current&(owned|prior_support):raise relation.RelationError('EPK sequence writes alias prior loop/window support')
                    if rows.intersection(stage['rows']) or prior_rows.intersection(stage['rows']):
                        raise relation.RelationError('EPK sequence original owned rows overlap')
                    owned.update(current);writes.update(current);rows.update(stage['rows'])
                    for row in stage['rows']:
                        prior_support.update(c for side in ('a','b') for c,_ in raw[row][side])
                prior_rows.update(rows);loop_writes.update(writes)
                offset=window['index']-chunk['metadata']['window_start']
                incoming,_,outgoing=chunk['points'][offset]
                if programs and programs[-1]['output']!=incoming:raise relation.RelationError('EPK sequence source point adjacency')
                programs.append(dict(index=window['index'],input=incoming,output=outgoing,stages=stages,
                    writes=sorted(writes),rows=sorted(rows),folded_products=window['folded_products'],folded_quotients=window['folded_quotients']))
        if len(programs)!=126 or [p['index'] for p in programs]!=list(range(126)):
            raise relation.RelationError('EPK sequence exact126 local programs')
        kept=set(_loop_kept(kept,loop_writes,protected))
        if local_rows!=initial_rows|{r for p in programs for r in p['rows']}:
            raise relation.RelationError('EPK sequence original row coverage')
        prior_rows.update(initial_rows)
        for ordinal in range(8*scope_id,8*scope_id+8):
            selection=batch.page_selection(checked,extracted,ordinal)
            prior_support.update(c for row in selection['selected_rows'] for side in ('a','b') for c,_ in row[side])
        first=scope['chunks'][0]['metadata']
        # Actual generator object/SDK scalar roles remain source references,
        # not an assumed prime-order or native-EPK result for this input.
        loops.append(dict(scope_id=scope_id,lane=scope['lane'],slot=scope['slot'],programs=programs,
            initial_rows=sorted(initial_rows),rows=sorted(local_rows),kept=sorted(kept),writes=sorted(loop_writes),
            scalar_source=first['randomizer'],bit_sources=first['bits'],native_generator=first['base'],
            published_sources=first['published'],computed_sources=first['output'],inverse_source=first['inverse']))
    if all_rows!={row['row'] for row in extracted['selected_rows']}:
        raise relation.RelationError('EPK sequence shared extraction coverage')
    return dict(parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],loops=loops,
        rows=sorted(all_rows),writes=sorted(owned),protected_public_committed_copy=[0,1,2,200692],
        universal_frame='For every column outside the exact union writes, mixed run agrees with its initial seed; for every LC/row whose support is outside, eval/satisfaction transport follows symbolically.',
        required_kernel_prerequisites=['Construct all6 canonical scalar bit/comparator rows from native Fr seeds, no prior Satisfies premise',
            'Prove each actual local window constructor and derive outgoing native recurrence from rows',
            'Seed published EPK from the same native SDK generator/scalar objects; derive bound/inverse rows',
            'Prove exact original supported LC freshness and whole outside-row frame, not by a digest'],
        scope='Exact6x126 local ownership/adjacency recipe; independent canonical/native/local kernel/frame instantiation OPEN')
