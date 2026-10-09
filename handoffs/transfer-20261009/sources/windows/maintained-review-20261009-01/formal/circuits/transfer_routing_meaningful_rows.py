"""Recover only uniquely checked physical zero-test and routing OR operands."""
from . import transfer_routing_rows as routing, transfer_relation as relation
from .transfer_fixed_spend import canonical, combine

SCHEMA='shieldd-transfer-routing-meaningful-rows-v1'


def extract(manifest,page,permutation,stream,accepted,params,base):
    selected=routing.boundaries(manifest,page,permutation,accepted,params)
    checked=selected['checked'];records=checked['records']
    def value(ref):
        kind,handle=routing.pages.reference(ref)
        return canonical([(0,handle)]) if kind=='native' else checked['observed'][handle]
    regulated,change=[value(ref) for ref in records['routing','shared',0][:2]]
    flags=[value(ref) for ref in records['routing','flags',0]]
    swap,first,second=flags[:3];one=((0,1),);copy=checked['metadata']['constant_copy']
    touched={c for lc in [regulated,change,swap,first,second] for c,_ in lc}
    raw={};normalized={};terms=0
    def observe(row):
        nonlocal terms
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ['a','b'])
        if not(any(c in touched for c,_ in a) or (len(a)<=6 and len(b)<=6)):return
        terms+=len(a)+len(b)
        if len(raw)>=routing.MAX_ROWS or terms>routing.MAX_TERMS:
            raise relation.RelationError('bounded routing meaningful candidate pool')
        raw[row['row']]=(a,b)
        normalized[row['row']]=tuple(canonical((0 if c==copy else c,v) for c,v in lc) for lc in [a,b])
    identity=relation.inspect(stream,expected_relation=checked['metadata']['relation_digest'],row_observer=observe)
    assert identity==base['identity'] and selected['metadata_sha256']==base['metadata_sha256']
    table=routing._Rows(raw,normalized,copy)
    links=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    assert len(links)==1
    negative=lambda lc:{c for c,v in lc if v==relation.MODULUS-1 and c not in [0,copy]}
    zero_candidates=[]
    for column in sorted(negative(first)&negative(second)):
        zero=((column,1),)
        if len(table.by_row.get((zero,zero),[]))!=1:continue
        products=table.products(change,zero,())
        if len(products)==1:zero_candidates.append((zero,products[0]))
    if len(zero_candidates)!=1:raise relation.RelationError('unique actual change zero operand required')
    zero,zero_product=zero_candidates[0];has_change=combine(one,zero,-1)
    inverses=[]
    occupied={c for lc in [regulated,change,swap,zero] for c,_ in lc}|{0,copy}
    for a in table.by_a:
        for sign in [1,-1]:
            inverse=combine(change,a,-sign)
            if len(inverse)!=1 or inverse[0][1]!=1 or inverse[0][0] in occupied:continue
            for product in table.products(change,inverse,has_change):
                inverses.append(dict(inverse=inverse,certificate=product))
    if len(inverses)!=1:raise relation.RelationError('unique actual change reciprocal operand required')
    inverse=inverses[0]
    combinations=[]
    for regulator in table.pairs(regulated,has_change):
        sender=combine(combine(regulated,has_change),regulator['output'],-1)
        target0=combine(combine(swap,sender),first,-1)
        other_swap=combine(one,swap,-1)
        target1=combine(combine(other_swap,sender),second,-1)
        left=[p for p in table.pairs(swap,sender) if p['output']==target0]
        right=[p for p in table.pairs(other_swap,sender) if p['output']==target1]
        if len(left)==len(right)==1:
            combinations.append(dict(sender=sender,regulator=regulator,first=left[0],second=right[0]))
    if len(combinations)!=1:raise relation.RelationError('unique captured meaningful OR chain required')
    chain=combinations[0]
    booleans=dict(regulated=table.exact(regulated,regulated,'regulated Boolean'),
                  swapped=table.exact(swap,swap,'swapped Boolean'),
                  zero=table.exact(zero,zero,'change zero Boolean'))
    used={links[0],*booleans.values()}
    for product in [zero_product,inverse['certificate'],chain['regulator'],chain['first'],chain['second']]:
        used.update(product['rows'])
    rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in raw[i][0]],
                       b=[[c,f'{v:064x}'] for c,v in raw[i][1]]) for i in sorted(used)]
    return dict(schema=SCHEMA,identity=identity,metadata_sha256=selected['metadata_sha256'],
                selected_rows=rows,plan=dict(regulated=regulated,change=change,swapped=swap,
                meaningful=[first,second],zero=zero,has_change=has_change,zero_product=zero_product,
                inverse=inverse,chain=chain,booleans=booleans,constant_link=links[0]),
                candidate_rows=len(raw),candidate_terms=terms,source_only=True,kernel_run=False,
                scope='Uniquely observed physical change zero-test and three OR products; native/source/caller/full Transfer OPEN')
