"""All65 exact variable-window ownership and native-table construction plan.

Five derivative pages are reaccepted against their genuine qualifier and
single original-row replay. This never invents canonical bits, denominator
truth, a native endpoint or qualification flags. The local generators consume
this plan after capture; signed/native/full outside-frame joins stay explicit.
"""
from . import transfer_balance_variable as variable,transfer_balance_variable_batch as batch
from . import transfer_balance_variable_completion as completion,transfer_relation as relation


def _rows(extracted,indices):
    raw={row['row']:tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        for row in extracted['selected_rows']}
    if not set(indices)<=set(raw):raise relation.RelationError('balance65 missing original local row')
    return {index:raw[index] for index in indices}


def _writes(plan):
    return {column for stage in plan['stages'] for column in
        ([stage['output']] if stage['kind'] in ('square','linear') else
         [stage['output'],stage['auxiliary']] if stage['kind']=='product' else
         [stage['quotient'],stage['product'],stage['auxiliary']])}


def _retain(prior,rows):
    for index,row in rows.items():
        if index in prior and prior[index]!=row:raise relation.RelationError('balance65 original shared row changed')
        prior[index]=row


def plan(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base,
        extracted,readonly_lcs=(),*,compiler_origin=22738):
    checked=variable.inspect_pages(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base)
    relation.natural(compiler_origin,checked['parent']['domain_size'])
    selections=[batch.page_selection(checked,extracted,ordinal) for ordinal in range(5)]
    first=checked['chunks'][0];copy=checked['parent']['constant_copy']
    table=completion.window_plan(first,selections[0],0,True,readonly_lcs)
    groups=[group for group in table['point_groups'] if group['index'] in (0,1)]
    if len(groups)!=2:raise relation.RelationError('balance65 exact precompute two groups')
    table_stages=[stage for group in groups for stage in table['stages'][group['stage_start']:group['stage_end']]]
    table_rows=set(table['constant_rows'])|{row for stage in table_stages for row in stage['rows']}
    table_plan=dict(table,stages=table_stages,local_rows=sorted(table_rows),point_groups=groups)
    native=first['points']['base']
    if any(value[0]!='source' or len(first['derived'][value[1]])!=1 or first['derived'][value[1]][0][1]!=1 for value in native):
        raise relation.RelationError('balance65 exact native asset coordinate seed singletons')
    seed=[first['derived'][value[1]][0][0] for value in native]
    if len(set(seed))!=2 or set(seed)&{0,1,2,copy}:
        raise relation.RelationError('balance65 native seed aliases shared columns')
    owned=_writes(table_plan)|set(seed);prior=_rows(selections[0],table_rows)
    protected={0,1,2,6,copy}|{c for terms in readonly_lcs for c,_ in terms}
    for handle in first['bits']:protected.update(c for c,_ in first['derived'][handle])
    for role in ('negative','magnitude'):
        value=first[role]
        if value[0]=='source':protected.update(c for c,_ in first['derived'][value[1]])
    if owned&protected:raise relation.RelationError('balance65 seed/precompute aliases signed/public/shared roles')
    programs=[];previous=None;cursor=None
    for ordinal,(page,selection) in enumerate(zip(checked['chunks'],selections)):
        for offset in range(page['metadata']['window_count']):
            local=completion.window_plan(page,selection,offset,False,readonly_lcs)
            index=local['window_index'];writes=_writes(local);rows=_rows(selection,local['local_rows'])
            if index!=len(programs):raise relation.RelationError('balance65 exact ordered complete windows')
            if writes&(protected|owned):raise relation.RelationError('balance65 local writes overlap earlier/signed/shared columns')
            if any(c in writes for row in prior.values() for terms in row for c,_ in terms):
                raise relation.RelationError('balance65 later writes destroy earlier original row support')
            if previous is not None and page['windows'][offset][0]!=previous:
                raise relation.RelationError('balance65 source endpoint adjacency')
            low=[c for c in writes if c<compiler_origin];high=[c for c in writes if compiler_origin<=c<copy]
            if not low or not high or len(low)+len(high)!=len(writes):
                raise relation.RelationError('balance65 exact dual allocation windows')
            before=(min(low),min(high));after=(max(low)+1,max(high)+1)
            if cursor is not None and any(a>b for a,b in zip(cursor,before)):
                raise relation.RelationError('balance65 allocation cursors moved backwards')
            if any(not(c<before[0] or compiler_origin<=c<before[1] or c==copy)
                   for row in prior.values() for terms in row for c,_ in terms):
                raise relation.RelationError('balance65 previous original supports exceed actual next frame')
            programs.append(dict(index=index,page_ordinal=ordinal,window_offset=offset,plan=local,
                writes=sorted(writes),rows=sorted(rows),before_frame=before,after_frame=after,
                incoming=page['windows'][offset][0],outgoing=page['windows'][offset][4],bits=page['window_bits'][offset]))
            owned.update(writes);_retain(prior,rows);cursor=after;previous=page['windows'][offset][4]
    if len(programs)!=65 or previous!=first['points']['output']:
        raise relation.RelationError('balance65 original full loop endpoint')
    return dict(checked=checked,selections=selections,precompute=table_plan,seed_writes=seed,
        programs=programs,writes=sorted(owned),protected=sorted(protected),rows=sorted(prior),
        parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],identity=extracted['identity'],
        scope='Exact native-table/precompute65 owned source rows/frames only; native seed same-value to preceding map, signed bits/native recurrence and full Transfer frame OPEN')
