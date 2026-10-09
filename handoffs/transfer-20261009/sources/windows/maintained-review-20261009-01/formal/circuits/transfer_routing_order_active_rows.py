"""Strict physical32 ordering and32 active-prefix row correspondence.

Source operands come from the validated routing role page. No missing operand
or physical row is guessed; semantic and native proofs remain separate.
"""
import hashlib,json
from . import transfer_routing_rows as routing, transfer_relation as relation
from .transfer_fixed_spend import canonical,combine

SCHEMA='shieldd-transfer-routing-order-active-rows-v1'


def extract(manifest, page, permutation, stream, accepted, params, base):
    selected = routing.boundaries(manifest,page,permutation,accepted,params)
    checked = selected['checked']
    def value(ref):
        kind,handle=routing.pages.reference(ref)
        return canonical([(0,handle)]) if kind=='native' else checked['observed'][handle]
    records=checked['records']
    regulated=value(records['routing','shared',0][0])
    active=[value(ref) for ref in records['routing','active-prefix',0]]
    prefixes=[[value(ref) for ref in records['routing',tag,0]]
              for tag in ['regulated-prefix','unregulated-prefix']]
    assert len(active)==32 and all(len(items)==32 for items in prefixes)
    assert base['schema']==routing.SCHEMA
    assert base['metadata_sha256']==selected['metadata_sha256']
    for slot in range(2):
        assert canonical(base['plan']['precision'][slot]['input'])==selected['precision'][slot]['input']
        assert [canonical(lc) for lc in base['plan']['precision'][slot]['prefix']]==prefixes[slot]
    copy=checked['metadata']['constant_copy']
    touched={column for group in [prefixes[0],prefixes[1],active,[regulated]]
             for lc in group for column,_ in lc}
    raw={};normalized={};terms=0
    def observe(row):
        nonlocal terms
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ['a','b'])
        if not (any(c in touched for c,v in a) or (len(a)<=6 and len(b)<=6)):
            return
        terms+=len(a)+len(b)
        if len(raw)>=routing.MAX_ROWS or terms>routing.MAX_TERMS:
            raise relation.RelationError('bounded order/active row pool exceeded')
        raw[row['row']]=(a,b)
        normalized[row['row']]=tuple(canonical((0 if c==copy else c,v) for c,v in lc) for lc in [a,b])
    identity=relation.inspect(stream,expected_relation=checked['metadata']['relation_digest'],row_observer=observe)
    assert identity==base['identity']
    table=routing._Rows(raw,normalized,copy)
    one=((0,1),)
    links=[index for index,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(links)!=1:raise relation.RelationError('unique actual copy assertion required')
    regulated_row=table.exact(regulated,regulated,'routing regulated Boolean')
    used={links[0],regulated_row};steps=[]
    for index in range(32):
        first,second=prefixes[0][index],prefixes[1][index]
        ordering=table.product(first,combine(one,second,-1),'precision order '+str(index),())
        difference=combine(first,second,-1)
        target=combine(active[index],second,-1)
        candidates=[pair for pair in table.pairs(regulated,difference) if pair['output']==target]
        if len(candidates)!=1:raise relation.RelationError('unique exact source active select product '+str(index))
        select=candidates[0]
        boolean=table.exact(active[index],active[index],'active prefix Boolean '+str(index))
        used.update(ordering['rows']);used.update(select['rows']);used.add(boolean)
        steps.append(dict(index=index,regulated_prefix=first,unregulated_prefix=second,
                          active=active[index],ordering=ordering,select=select,boolean_row=boolean))
    selected_rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in raw[i][0]],
                               b=[[c,f'{v:064x}'] for c,v in raw[i][1]]) for i in sorted(used)]
    return dict(schema=SCHEMA,identity=identity,metadata_sha256=selected['metadata_sha256'],
                source_sha256=hashlib.sha256(page).hexdigest(),selected_rows=selected_rows,
                plan=dict(regulated=regulated,regulated_boolean=regulated_row,constant_link=links[0],steps=steps),
                candidate_rows=len(raw),candidate_terms=terms,source_only=True,kernel_run=False,
                scope='Exact physical32 ordering and32 active select/Boolean rows; semantic/native/hash/tag/full Transfer open')
